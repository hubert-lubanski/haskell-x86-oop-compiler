{-# LANGUAGE CPP #-}
module Debugging where
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad (when)
import Debug.Trace (traceIO)
import Common (altgreenColor)

#ifdef __TRACE_LEVEL__
tracing = __TRACE_LEVEL__
#else
tracing = 0
#endif

#ifdef DODEBUG
debugging = True
#else
debugging = False
#endif


debug :: MonadIO m => String -> m ()
debug str = when debugging $ liftIO $ traceIO str
debugTrace i str = when (tracing <= i) $ liftIO $ traceIO (altgreenColor "trace: " ++ str)