module Error where
import Grammar.Abs
import Common
import Control.Monad
import Control.Monad.Except
import GHC.Stack ( HasCallStack )
import Debug.Trace (traceIO)
import GHC.IO.Unsafe (unsafePerformIO)
import System.Process (system)
import qualified GHC.IO.Exception as GIExcept

type Position = BNFC'Position
type Message = String

newtype Err = Err (Position, Message)
instance Show Err where
    show (Err (pos,msg)) = case pos of
        Nothing         -> msg
        Just (row, col) -> altredColor "[BŁĄD]: " ++ cyanColor "Linia " ++ show row ++ ", kolumna " ++  show col ++ ":\n" ++ defaultColor ++ msg

makeCustomError :: (HasCallStack, MonadError Err m) => String -> Position -> [Char] -> m a
makeCustomError err pos msg = throwError $ Err (pos, _redColor ++ "[" ++ err ++ "]: " ++ defaultColor ++ msg)
makeError pos msg = throwError $ Err (pos, _redColor ++ "[Error]: " ++ defaultColor ++ msg)

willNeverHappen :: HasCallStack => a
willNeverHappen = error (altredColor "[FATAL]: " ++ yellowColor "This should have never happened!" ++ defaultColor)

printCodeFragment :: Int -> Int -> String -> [String]
printCodeFragment x y code =
    let lcode = lines code
        n = min 0 (x - 1)
    in
        take 5 $ drop n lcode
    where
        drop _ [] = []
        drop 0 ys = ys
        drop x (y:ys) = drop (x-1) ys

typeError :: (HasCallStack, MonadError Err m) => Position -> String -> m a
typeError = makeCustomError "Type Error"

referenceError :: (HasCallStack, MonadError Err m) => Position -> String -> m a
referenceError = makeCustomError "Reference Error"

fieldError :: (HasCallStack, MonadError Err m) => Position -> String -> m a
fieldError = makeCustomError "Field Error"

castError :: (HasCallStack, MonadError Err m) => Position -> String -> m a
castError = makeCustomError "Cast Error"


{-# NOINLINE waltIDontKnowMan #-}
waltIDontKnowMan :: HasCallStack => a
waltIDontKnowMan = unsafePerformIO $! do
    putStrLn msg
    void $ system "play -v 0.15 \"~/waltIDontKnowMan.mp3\" 2>/dev/null"
    error ""
    
    where msg = altmagentaColor "\n\n[SUS ERROR]:\n"
              ++ altyellowColor "\tWalt, I don't know man.\n"
              ++ "\tYou've been seeming sus lately.\n"
              ++ "\tIt's almost like we have an " ++ altredColor "imposter"
              ++ altblackColor  " among us.\n"
              ++ "\tI saw that you wan-\n"
              ++ redColor
                 "\n\tDON'T LIE TO ME WALT!\n\n"