{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

-- | A test suite that just checks whether modules type-check or not
-- as expected. The expectation is determined by which directory the
-- test case is in.

module Main (
  main,
  ) where

import Bag
import DynFlags
import ErrUtils (ErrorMessages,errDocImportant,errMsgDoc)
import GHC
import GHC.LanguageExtensions.Type (Extension(..))
import GHC.Paths (libdir)
import GhcMonad (withTempSession)
import HscTypes (srcErrorMessages)
import MonadUtils (liftIO)
import Outputable

import Control.Monad (when,void)
import Data.Char (isDigit)
import Data.Either (partitionEithers)
import qualified Data.IntSet as IntSet
import Data.List (isPrefixOf)
import System.Directory (doesFileExist,listDirectory)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath.Posix ((</>),splitPath,takeBaseName,takeDirectory,takeExtension)

languageExtension :: Extension -> DynFlags -> DynFlags
languageExtension = flip xopt_set

plugin :: String -> DynFlags -> DynFlags
plugin s dflags = dflags{pluginModNames = pn : pluginModNames dflags}
  where
  pn = mkModuleName s

pluginOpts :: String -> [String] -> DynFlags -> DynFlags
pluginOpts s ss dflags = dflags{pluginModNameOpts = map ((,) pn) ss ++ pluginModNameOpts dflags}
  where
  pn = mkModuleName s

expose :: String -> DynFlags -> DynFlags
expose p dflags = dflags{packageFlags = pf : packageFlags dflags}
  where
  pf = ExposePackage ("-package " ++ p) (PackageArg p) (ModRenaming True [])

noWarnings :: DynFlags -> DynFlags
noWarnings dflags = dflags{warningFlags = IntSet.empty}

includePath :: String -> DynFlags -> DynFlags
includePath path dflags = dflags{includePaths = path : includePaths dflags}

modifySessionDynFlags :: (DynFlags -> DynFlags) -> Ghc ()
modifySessionDynFlags f = getSessionDynFlags >>= void . setSessionDynFlags . f

-----

data E = MkE {quietly :: Bool}

main :: IO ()
main = defaultErrorHandler defaultFatalMessager defaultFlushOut $ runGhc (Just libdir) $ do
  args0 <- liftIO getArgs
  let (opts,args1) = partitionEithers $ map (\case ':':opt -> Left opt; s -> Right s) args0

  _ <- modifySessionDynFlags $
      id
    . languageExtension TypeOperators
    . languageExtension TypeFamilies
    . languageExtension ExplicitForAll
    . languageExtension ScopedTypeVariables
    . languageExtension FlexibleContexts
    . languageExtension DataKinds
    . plugin "Coxswain"
    . pluginOpts "Coxswain" opts
    . expose "coxswain"
    . noWarnings
    . (\x -> x{hscTarget = HscInterpreted,ghcLink = LinkInMemory,ghcMode = CompManager})

  let e = MkE{quietly=True}
  r <- case args1 of
    [] ->
          mappend
      <$>
          runTestDir e IllTyped
      <*>
          runTestDir e WellTyped
    [path] -> runGivenTest e{quietly=False} path
    paths -> mconcat <$> mapM (runGivenTest e) paths

  liftIO $ do
    putStrLn ""
    putStrLn $ "#BAD        " ++ show (bad r)
    putStrLn $ "#EXPECTED   " ++ show (expected r)
    putStrLn $ "#UNEXPECTED " ++ show (unexpected r)
    putStrLn ""
    putStrLn $ "#Total      " ++ show (total r)

    if total r == expected r then return () else exitFailure

data Results = MkResults {bad,expected,unexpected :: !Int}

instance Monoid Results where
  mempty = MkResults {bad=0,expected=0,unexpected=0}
  mappend r1 r2 = MkResults {
       bad = bad r1 + bad r2
    ,
       expected = expected r1 + expected r2
    ,
       unexpected = unexpected r1 + unexpected r2
    }

bad1 :: String -> Ghc Results
bad1 msg = mempty{bad=1} <$ liftIO (putStrLn $ "<BAD>        " ++ msg)

expected1 :: String -> Ghc Results
expected1 msg = mempty{expected=1} <$ liftIO (putStrLn $ "<EXPECTED>   " ++ msg)

unexpected1 :: String -> Ghc Results
unexpected1 msg = mempty{unexpected=1} <$ liftIO (putStrLn $ "<UNEXPECTED> " ++ msg)

total :: Results -> Int
total (MkResults a b c) = a + b + c

data TestKind = IllTyped | WellTyped
  deriving (Read,Show)

runTestDir :: E -> TestKind -> Ghc Results
runTestDir e tk = do
  let dir = "test" </> (case tk of IllTyped -> "ill-typed"; WellTyped -> "well-typed")
  let is_hs_file s = case takeExtension s of
        ".hs" -> True
        ".lhs" -> True
        _ -> False
  paths <- map (dir </>) <$> filter is_hs_file <$> liftIO (listDirectory dir)
  mconcat <$> mapM (runTest e tk) paths

runGivenTest :: E -> String -> Ghc Results
runGivenTest e path
  | "test/ill-typed/" `isPrefixOf` path = proceed IllTyped
  | "test/well-typed/" `isPrefixOf` path = proceed WellTyped
  | otherwise = bad1 $ path ++ " is not prefixed by test/{ill,well}-typed/."
  where
  proceed tk = do
    present <- liftIO $ doesFileExist path
    if present then runTest e tk path else bad1 (path ++ " is not a file.")

validTestName :: String -> Bool
validTestName path = case takeBaseName path of
  'T':ds@(d0:ds1) -> (null ds1 || d0 /= '0') && all isDigit ds
  _ -> False

runTest :: E -> TestKind -> String -> Ghc Results
runTest e tk path

  | not (validTestName path) = bad1 $ path ++ " is named incorrectly."

  | otherwise = withTempSession id $ do
  modifySessionDynFlags $ foldr (.) id [ includePath (dir </> "aux") | dir <- splitPath (takeDirectory path) ]
  guessTarget path Nothing >>= setTargets . (:[])
  let thisModuleName = mkModuleName "Main"
  load (LoadDependenciesOf thisModuleName) >>= \case
    Failed -> bad1 $ path ++ " could not be executed because its dependencies fail to build."
    Succeeded -> do
      errors <- handleSourceError (return . srcErrorMessages) $
        emptyBag <$ (getModSummary thisModuleName >>= parseModule >>= typecheckModule)
      when (not (quietly e)) $ getSessionDynFlags >>= \dflags -> liftIO $ do
        mapM_ putStrLn [ showSDocOneLine dflags (hcat (errDocImportant doc)) | doc <- map errMsgDoc (bagToList errors) ]
      judgeTest tk path errors

judgeTest :: TestKind -> String -> ErrorMessages -> Ghc Results
judgeTest tk path errors = do
  let welltyped = isEmptyBag errors
  let testFailed = case tk of
        IllTyped -> welltyped
        WellTyped -> not welltyped
  let status = if welltyped then "well" else "ill"
  let msg = path ++ " is " ++ status ++ "-typed."
  if testFailed then unexpected1 msg else expected1 msg
