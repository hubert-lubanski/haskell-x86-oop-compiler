{-# LANGUAGE CPP #-}
module Main where
import System.Environment (getArgs)
import qualified Data.Map as M
import Grammar.Par
import Grammar.Lex
import Intermediate (prepareForCompilation, staticStringsCode, virtualTablesCode)
import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.Reader (ReaderT(runReaderT))
import Control.Monad.State (StateT(runStateT))
import Control.Monad.Except (runExceptT, ExceptT)
import Control.Monad
import Types
import Common
import Error
import Distribution.Compat.Prelude (exitFailure, exitSuccess, fromMaybe, sortBy, isPrefixOf)
import Data.Map (mapWithKey)
import Grammar.Abs
import System.IO ( hPutStrLn, stderr )
import SSATransformation
    (makeCFG, runCFGGenerator, transformToSSA )
import qualified SSATransformation as SSA

import Machine
import qualified Machine as X86

import qualified Data.Set as S
import GHC.Stack (HasCallStack)
import System.FilePath (takeBaseName, dropExtension)
import System.Process (system)
import System.Directory (getCurrentDirectory)
import Debugging (debugTrace)
import System.Console.GetOpt

#ifdef __LIB_PATH__
absoluteLibraryPath = __LIB_PATH__
#else
absoluteLibraryPath = error "Path to library not supplied"
#endif


printStderr = hPutStrLn stderr

compilerError :: IO ()
compilerError = do
    hPutStrLn stderr "ERROR"

compilerOK = do
    hPutStrLn stderr "OK"


runGenerator genM = runReaderT (
                        runStateT (
                            runExceptT genM
                        ) gState
                    ) gEnv

codeVeryHuman :: HasCallStack => (String -> IO ()) ->M.Map Integer (Label,[String]) -> IO ()
codeVeryHuman writeLn codes = do

    forM_ (M.assocs codes) (\(_, (label, c)) -> do
        unless (label == SSA.dummyNodeLabel) $ do
            -- putStrLn (label ++ " <" ++ show (position $ cfg ?! label) ++ ">")
            writeLn (label ++ ":")
            if null c then writeLn "\t; empty\n"
            else writeLn $ concatMap ("\t" ++) c
        )
        




runCompiler :: Integer -> FilePath -> IO b
runCompiler worklevel filename = do
    input <- readFile filename
    let program = myLexer input
    case pProgram program of
        Left err -> do
            compilerError
            printStderr "Błąd parsowania:\n"
            mapM_ (printStderr . showPosToken . mkPosToken) program
            printStderr err
            exitFailure
            where
                showPosToken ((l,c),t) = concat [ show l, ":", show c, "\t", show t ]

        Right tree -> do
            putStrLn "Parsowanie: OK\n"
            unless (worklevel > 0) exitSuccess

            x <- runGenerator $ prepareForCompilation tree
            printGeneratorResult x input
            let state = snd x
                f_codes = filter (not . dummyFunction . snd . (funcLabels state ?!) . fst) 
                        $ M.toList (functionsCode state)
                extern_functions = map snd
                                 $ filter (dummyFunction . snd)
                                          (M.elems $ funcLabels state)
            
            unless (worklevel > 1) exitSuccess

            control_flow_graphs <- forM f_codes (\(name, code) -> do
                cfg <- runCFGGenerator (makeCFG 0 (getS name) code)
                return (cfg, name)
                )


            ssacfgs_and_mappings <- forM control_flow_graphs (\(cfg, name) ->
                    transformToSSA (fst $ funcLabels state ?! name)
                                   (maxRegCounter state) cfg
                )
            
            unless (worklevel > 2) exitSuccess

            machine_codes <- forM ssacfgs_and_mappings (\(ssacfg, entryMappings) -> do
                mcfg <- calcLiveness ssacfg
                simpleRegisterAllocation entryMappings mcfg
                )

            -- machine_codes <- forM f_codes (\(name,code) -> do
            --     cfg <- runCFGGenerator (makeCFG 0 (getS name) code)

            --     (ssacfg, entryMappings) <- transformToSSA (fst $ funcLabels state ?! name)
            --                                               (maxRegCounter state) cfg
            --     mcfg <- calcLiveness ssacfg

            --     simpleRegisterAllocation entryMappings mcfg
            --     )
                

            let fileBasename = (dropExtension filename)
                assemblyFile = (fileBasename ++ ".s")
                objectFile = (fileBasename ++ ".o")

            writeFile assemblyFile ""

            let writeToFile str = appendFile assemblyFile  str
                writeToFileLn str = do
                    writeToFile str
                    writeToFile "\n"
                

            writeToFileLn "global main"
            writeToFileLn "\n; ----------------------------------------\n"
            writeToFileLn "; extern functions:\n"
            forM_ extern_functions (\label ->
                writeToFileLn ("extern " ++ label)
                )

            writeToFileLn "\n; ----------------------------------------\n"
            writeToFileLn "section .rodata\n"
            mapM_ writeToFile (staticStringsCode (snd x))


            mapM_ writeToFile (virtualTablesCode (snd x))

            writeToFileLn "\n; ----------------------------------------\n"
            writeToFileLn "section .text\n"
            forM_ machine_codes (codeVeryHuman writeToFileLn)
            
            unless (worklevel > 3) exitSuccess

            system ("nasm -g -f elf64 " ++ assemblyFile ++ " -o " ++ objectFile)
            system ("gcc -g -Wall -z noexecstack " ++ absoluteLibraryPath ++ "/libinternals.c "
                    ++ objectFile ++ " -o " ++ fileBasename)

            system("rm " ++ objectFile)

            putStrLn "Current directory: "
            dir <- getCurrentDirectory
            putStrLn dir

            exitSuccess

    where
        dummyFunction x = "__lat_builtin_" `isPrefixOf` x

        printGeneratorResult (result, state) input = case result of
            Left err -> do
                compilerError
                printStderr $ "Sprawdzanie: " ++ show err
                -- let Error.Err(pos, msg) = err
                -- case pos of
                --     Nothing    -> return ()
                --     Just (x,y) -> do
                --         putStrLn (altblueColor "--- kod ---")
                --         mapM_ putStrLn (printCodeFragment x y input)
                --         putStrLn (altblueColor "--- kod ---")
                --         putStrLn ""
                exitFailure

            Right _ -> do
                compilerOK
                let labelsMap = funcLabels state
                    codeMap = functionsCode state
                    objectMap = objectsInfo state

                mapM_ printObject (M.assocs objectMap)

                mapM_ (printFunction codeMap) (M.assocs labelsMap)




                where printFunction codeMap (key,val)  = do
                        let (ftype, flabel) = val
                        putStrLn (show (retType ftype) ++ " " ++ flabel ++ " " ++ show (argTypes ftype))
                        forM_ (codeMap ?! key) (\s -> putStrLn $ "\t" ++ show s)
                        putStrLn ""

                      printObject (on, record) = do
                        putStrLn ("class " ++ getS on ++ ":")
                        putStrLn ("\tsize: " ++ show (objectSize record))
                        putStrLn "\tvars:"
                        forM_ (M.assocs (varOffsets record)) (\(vn, (vt, vo)) ->
                                putStrLn ("\t\t" ++ show vt ++ " " ++ getS vn ++ " @ " ++ show vo)
                            )
                        putStrLn "\tmethods:"
                        forM_ (M.assocs (methodTable record)) (\(mn, mo)->
                                putStrLn ("\t" ++ show mn ++ " at offset " ++ show mo)
                            )

vMajor = 3
vMinor = 0
vIter = 0
compilerVersion = show vMajor ++ "." ++ show vMinor ++ "." ++ show vIter

data Flag = Version 
          | Trace Integer
          | WorkLevel Integer
    deriving (Show, Eq)
    

options :: [OptDescr Flag]
options = 
    [
        Option ['w'] ["worklevel"] (ReqArg (WorkLevel .read) "level")
        ("Up to which faze should the compiler run.\n"
        ++"0 - parser only\n"
        ++"1 - frontend and quadruple generation\n"
        ++"2 - SSA transformation\n"
        ++"3 - Machine code generation (default)\n"
        ++"4 - Compile the program"),
        Option ['v'] ["version"] (NoArg Version) "Show version number"
    ]

usage = "Użycie: latc plik.lat"

compilerOpts :: [String] -> IO ([Flag], [String])
compilerOpts argv = case getOpt Permute options argv of
    (o, n, []) -> return (o,n)
    (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
    where header = "Usage: latc_x86_64 [OPTION...] file.lat"
main :: IO ()
main = do
    args <- getArgs
    (flags, nonopts) <- compilerOpts args
    
    when (Version `elem` flags) $ do
        putStrLn ("Current compiler version: " ++ compilerVersion)
        exitSuccess
    


    case nonopts of
        [filename] -> 
            runCompiler (getWorkLevel flags) filename
        _          -> do
            compilerError
            printStderr usage
    

    where
        defaultWorkLevel = 4
        getWorkLevel [] = defaultWorkLevel
        getWorkLevel ((WorkLevel w):rest) = w
        getWorkLevel (_:rest) = getWorkLevel rest