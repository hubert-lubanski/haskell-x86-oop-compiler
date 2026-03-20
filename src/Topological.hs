import Types
import qualified Data.Map as M
import Data.Map (Map)
import Error (waltIDontKnowMan)

type SortedCode = (Integer, QuadCode)

topoCode :: [QuadCode] -> [SortedCode]
topoCode code = _topoCode code M.empty
    where
        _topoCode [] m = M.elems m
        _topoCode [c:cs] m = waltIDontKnowMan