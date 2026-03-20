module SSATransformation where
import Types
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad.State (MonadState (get, put), StateT (runStateT), evalStateT,  execStateT, modify, execState, State, gets, runState, evalState, MonadIO (liftIO))
import Error
import Debugging
import Common
import Grammar.Par
import Grammar.Abs
import Intermediate
import Control.Monad
import Data.Maybe (fromMaybe, listToMaybe, isNothing, isJust, fromJust)
import System.Exit
import Debug.Trace (traceM, trace, traceIO)
import GHC.Num (integerLogBase)
import Data.Bifunctor (Bifunctor(second))
import Data.List (sortOn, sortBy)
import GHC.Stack (HasCallStack)
import Data.Tuple (swap)

{-------------------------------------------------------------------------------
                    Graf przepływu sterowania
-------------------------------------------------------------------------------}

(@!) :: HasCallStack => [a] -> a
(@!) x = fromMaybe listError (listToMaybe x)
    where listError = error "Given list is empty!"

entryNode :: HasCallStack => ControlFlowGraph -> CFGNode
entryNode cfg = (@!) $ M.elems $ M.filter (( == 0) . position) cfg

data CFGNode = CFGNode {
    position :: Integer,
    entryLabel :: Label,
    instructions :: [QuadCode],
    exits :: Set Label,
    entries :: Set Label
}

type CFGGeneratorM a = StateT ControlFlowGraph IO a

emptyNode i label = CFGNode i label [] S.empty S.empty

type ControlFlowGraph = Map Label CFGNode

instance Show CFGNode where
    show node = "Block starting at <" ++ entryLabel node ++ ">\n"
              ++ unlines (map (("\t" ++). show) (instructions node))
              ++ "----\n"
              ++ "Entires:\n"
              ++ concatMap ((++ ", ") . show) (entries node)
              ++ "\nExits:\n"
              ++ concatMap ((++ ", ") . show) (exits node)
              ++ "\n"

prettyPrintCode :: CFGNode -> String
prettyPrintCode n = unlines (map (("\t" ++). show)
                            ((InsertLabel (entryLabel n)-:):instructions n))

cfgShowCodeHuman :: ControlFlowGraph -> IO ()
cfgShowCodeHuman cfg = do
    let asList = sortBy (\a b -> compare (position a) (position b)) (M.elems cfg)
    forM_ asList (\n -> do
        let label = entryLabel n
        {- unless (label == dummyNodeLabel) $ -}
        do
            -- putStrLn (label ++ " <" ++ show (position $ cfg ?! label) ++ ">")
            traceIO (label ++ ":\n")
            traceIO $ (prettyPrintCode n ++ "\n")
        )
    -- where
    --     _nodeShow :: [CFGNode] -> Set Label -> [String]
    --     _nodeShow [] _ = [""]
    --     _nodeShow (node:rest) visited =
    --         if S.member (entryLabel node) visited then
    --             _nodeShow rest visited
    --         else
    --             let ancestors = map (cfg ?!) $ S.toList (exits node)
    --                 newVisited = S.insert (entryLabel node) visited
    --             in
    --             prettyPrintCode node:_nodeShow (ancestors ++ rest) newVisited



nodeAddInstr :: CFGNode -> QuadCode -> CFGNode
nodeAddInstr node instr = node{instructions = instr:instructions node}

nodeAddExit :: CFGNode -> Label -> CFGNode
nodeAddExit node label = node{exits = S.insert label (exits node)}

nodeAddEntry :: CFGNode -> Label -> CFGNode
nodeAddEntry node label = node{entries = S.insert label (entries node)}

skipPastNextLabel :: [QuadCode] -> (Maybe Label, [QuadCode])
skipPastNextLabel [] = (Nothing, [])
skipPastNextLabel (instr:rest) = case instr of
    (FlowCtrlCode (InsertLabel label))  -> (Just label, rest)
    (Commented c _) -> skipPastNextLabel (c:rest)
    _   -> skipPastNextLabel rest


makeSimpleBlock :: CFGNode -> [QuadCode] -> (CFGNode, Maybe Label, [QuadCode])
makeSimpleBlock node code =
    let (cfgNode, nlabel, rest) = _makeSimpleBlock node code in
        (cfgNode{instructions = reverse (instructions cfgNode)}, nlabel, rest)

_makeSimpleBlock :: CFGNode -> [QuadCode] -> (CFGNode, Maybe Label, [QuadCode])
_makeSimpleBlock node [] =
    -- Doszliśmy do końca funkcji void (nie wymaga return)
    (nodeAddInstr node (ReturnVoid -:), Nothing, [])
_makeSimpleBlock node (instr:rest) = case instr of
    (ValueCode _ _)     -> _makeSimpleBlock (nodeAddInstr node instr) rest
    (ReferenceCode _ _) -> _makeSimpleBlock (nodeAddInstr node instr) rest
    (Commented c _)     -> _makeSimpleBlock node (c:rest)
    (FlowCtrlCode fctrl)->
        -- Jeżeli jest to skok/return to znajdujemy kolejną etykietę
        -- i oznaczamy ją jako początek dalszego kodu
        -- Jeżeli trafiliśmy na etykietę, to nasz blok naturalnie przechodzi
        -- do kolejnego, a znaleziona etykieta jest początkiem dalszego kodu
        let
            newNode = nodeAddInstr node instr
            (nextLabel, followUpCode) = skipPastNextLabel rest
        in
        case fctrl of
            (Jump label)    ->
                (nodeAddExit newNode label, nextLabel, followUpCode)

            (Return _)      ->
                (newNode, nextLabel, followUpCode)

            ReturnVoid      ->
                (newNode, nextLabel, followUpCode)

            (ConditionalFull _ _ _ l1 l2) ->
                let finalNode = nodeAddExit (nodeAddExit newNode l1) l2 in
                    (finalNode, nextLabel, followUpCode)

            (InsertLabel label) ->
                (nodeAddExit node label, Just label, rest)



updateNodeEntries :: ControlFlowGraph -> ControlFlowGraph
updateNodeEntries cfg = _updateNodeEntries (M.elems cfg) cfg
    where
        _updateNodeEntries [] cfg = cfg
        _updateNodeEntries (node:rest) cfg =
            --trace ("Updating entries from node at " ++ (entryLabel node)) $
            let nodeExits = exits node in
                _updateNodeEntries rest (foldl (nodeFold (entryLabel node)) cfg nodeExits)

        nodeFold origLabel acc label =
                M.map (\node -> if entryLabel node == label then
                                    nodeAddEntry node origLabel
                                else
                                    node) acc



makeCFG :: Integer -> Label -> [QuadCode] -> CFGGeneratorM ()
makeCFG num entry code = do
    cfg <- get
    if null code then do
        -- Funkcja o pustym ciele
        when (M.size cfg /= 0) $ do
            debugTrace 10 ("Non empty function")
            debugTrace 0 (show cfg)
            waltIDontKnowMan


        put (M.insert entry (emptyNode num entry){instructions = [(ReturnVoid -:)]} cfg)
        modify updateNodeEntries
    else do
        let (newNode, nextLabel, rest) = makeSimpleBlock (emptyNode num entry) code

        put (M.insert (entryLabel newNode) newNode cfg)
        if isNothing nextLabel then do
            modify updateNodeEntries
        else if null rest then do
            let Just label = nextLabel
            cfg <- get

            put (M.insert label (emptyNode (num + 1) label){
                entries = S.singleton label,
                exits = S.singleton label,
                instructions = [(ReturnVoid -:)]
            } cfg)
                
            modify updateNodeEntries

        else do
            let Just label = nextLabel
            makeCFG (num + 1) label rest
        



runCFGGenerator cfgM = execStateT cfgM M.empty

trimmUntillEmpty :: [QuadCode] -> IO ()
trimmUntillEmpty code = _trimmUntillEmpty 1 code
    where
        _trimmUntillEmpty _ [] = return ()
        _trimmUntillEmpty i code = do
            putStrLn $ "Code trimm number " ++ show i
            let (_, removed_code) = skipPastNextLabel code
            forM_ removed_code (\s -> putStrLn $ "\t" ++ show s)
            putStrLn "---"
            _trimmUntillEmpty (i+1) (drop 1 removed_code)


{-------------------------------------------------------------------------------
    Transformacja do postaci SSA
-------------------------------------------------------------------------------}
data SSAVar = Valid | Reused | Unknown Variable

data SSABlockData = SSABlockData {
    mappings :: Map Variable Variable,
    defined :: Set Variable,
    unknown :: Map Variable Variable -- Oryginalna zmienna -> gdzie przypisać
}

instance Show SSABlockData where
    show block = "Mappings:\n"
               ++ M.foldMapWithKey (\k v -> show k ++ "->" ++ show v ++ "\n") (mappings block)
               ++ "Definitions:\n" ++ S.foldr (\e s -> show e ++ ", " ++ s) "" (defined block) ++ "\n"
               ++ "Unknowns:\n" ++ M.foldMapWithKey (\k v -> show k ++ "->" ++ show v ++ "\n") (unknown block) ++ "\n"

emptyBlockData = SSABlockData M.empty S.empty M.empty

data SSATransformerState = SSATState {
    variableIndex :: Integer,
    blockMappings :: Map Label SSABlockData,
    workingGraph :: ControlFlowGraph,
    visitedSet :: Set Label
}

emptyState :: Integer -> ControlFlowGraph -> SSATransformerState
emptyState val cfg = let emptyBlockDataMap = map (\k -> (k,emptyBlockData)) (M.keys cfg) in
                SSATState (10 * nearestPower10 val) (M.fromList emptyBlockDataMap) cfg S.empty

newSSALocation :: SSATransformerM Integer
newSSALocation = do
    number <- gets variableIndex
    modify (\s -> s{variableIndex = number + 1})
    return number

type SSATransformerM a = StateT SSATransformerState IO a

nearestPower10 :: Integer -> Integer
nearestPower10 val = _nearestPower10 1 ((toInteger $ integerLogBase 10 val) + 1)
    where _nearestPower10 a i | i < 0     = 0
                              | i == 0    = a
                              | otherwise =  _nearestPower10 (10*a) (i-1)

changeVariableLocation :: Location -> Variable -> Variable
changeVariableLocation newloc var = case var of
    (Local val)     -> Local (changeLocation newloc val)
    (Parameter val) -> Parameter (changeLocation newloc val)
    (Dereferenced var) -> Dereferenced (changeVariableLocation newloc var)
changeLocation newloc (Value _) = Value newloc
changeLocation newloc (Reference _) = Reference newloc


transformToSSA :: HasCallStack =>  FunType -> Integer -> ControlFlowGraph -> IO (ControlFlowGraph, Map Variable Variable)
transformToSSA fType val cfg = evalStateT (_transformToSSA fType cfg) (emptyState val cfg)


addParameterDefinitions :: Integer -> FunType -> [Variable]
addParameterDefinitions numbering ftype =
    let isRefArgs = map isReference (argTypes ftype)
        parameters = zipWith (\isRef num ->
                if isRef then Parameter (Reference num)
                else Parameter (Value num)
            ) isRefArgs [numbering..]
    in
        parameters

addDefaultMapping :: Integer -> [Variable] -> (Map Variable Variable, Integer)
addDefaultMapping base parameters =
    let x = zip parameters (map constructDeafaultVar parameters)
    in
    (M.fromList x, toInteger (length parameters) + base + 1)
    where
        constructDeafaultVar (Parameter (Value i)) = Parameter (Value (i+base))
        constructDeafaultVar (Parameter (Reference i)) = Parameter (Reference (i+base))

dummyNodeLabel = "%%parameter$dummy$node%%"

addDummyParameterNode :: HasCallStack => FunType -> SSATransformerM ()
addDummyParameterNode ftype = do
    graph <- gets workingGraph
    startNode <- gets (entryNode . workingGraph)

    let params = addParameterDefinitions 0 ftype
        newData = emptyBlockData{defined = S.fromList params}
        newNode = (emptyNode (-1) dummyNodeLabel){exits = S.singleton
                                                     (entryLabel startNode)}
        newStart = startNode{entries = S.insert dummyNodeLabel (entries startNode)}
        newGraph_ = M.insert dummyNodeLabel newNode graph
        newGraph = M.insert (entryLabel startNode) newStart newGraph_

    modify (\s -> s{workingGraph = newGraph,
                    blockMappings = M.insert dummyNodeLabel newData (blockMappings s)})


_transformToSSA :: HasCallStack => FunType -> ControlFlowGraph -> SSATransformerM (ControlFlowGraph, Map Variable Variable)
_transformToSSA ftype cfg = do
    modify (\s -> s{workingGraph = cfg})
    addDummyParameterNode ftype
    cfgSSAT_1 ftype

    cfg <- gets workingGraph

    -- forM_ cfg (liftIO . traceIO . show)
    -- bmap <- gets blockMappings
    -- forM_ (M.assocs bmap) (\(l,bd) -> do
    --     (liftIO . traceIO) l
    --     (liftIO . traceIO . show) bd
    --     )

    cfgSSAT_2

    -- (liftIO . traceIO) "--- Po SSA 2 ---"

    bmap <- gets blockMappings
    startMappings <- gets (mappings . (bmap ?!) . entryLabel . entryNode . workingGraph)
    -- forM_ (M.assocs bmap) (\(l,bd) -> do
    --     (liftIO . traceIO) l
    --     (liftIO . traceIO . show) bd
    --     )

    cfgSSAT_3

    cfg <- gets workingGraph

    return (cfg, startMappings)


getLhsSSAOperand :: Bool -> Operand -> Label -> SSATransformerM Operand
getLhsSSAOperand memaccess oldop blockLabel = case oldop of
    (Immediate _)   -> willNeverHappen
    (Undefined _)   -> willNeverHappen
    (Variable v)    -> do
        blockData <- gets ((flip (?!) blockLabel) . blockMappings)
        let
            swap = M.lookup v (mappings blockData)
            defi = S.member v (defined blockData)
            unkn = M.lookup v (unknown blockData)
        
        

        if not defi && isNothing unkn then do     -- Niezdefiniowana w tym bloku
            -- Tworzymy nową zmienną 
            newLoc <- newSSALocation
            let newVar = changeVariableLocation newLoc v

            -- i dodajemy do zdefiniowanych
            let newData = blockData{mappings = M.insert v newVar (mappings blockData),
                                    defined = S.insert v (defined blockData)}
            modify (updateBlockData blockLabel newData)

            return (Variable newVar)
        else do -- isNothing swap => Już zdefiniowana, ale tylko raz
                -- else           => efektywnie to samo

            if not memaccess then do -- o ile to nie odwołanie do pamięci:
                -- Tworzymy nową zmienną 
                newLoc <- newSSALocation
                let newVar = changeVariableLocation newLoc v

                -- i zapisujemy podmianę
                let newData = blockData{mappings = M.insert v newVar (mappings blockData)}
                modify (updateBlockData blockLabel newData)
                return (Variable newVar)
            else do
                -- Używamy tej samej zmiennej
                return $ Variable ((mappings blockData) ?! v)
                

    where updateBlockData label newData state =
            state{blockMappings = M.insert label newData (blockMappings state)}

-- Zdobądź nowy operand prawej strony
getRhsSSAOperand ::  Operand -> Label -> SSATransformerM Operand
getRhsSSAOperand oldop blockLabel = case oldop of
    (Immediate i)   -> return oldop
    (Undefined s)   -> return oldop
    (Variable v)    -> do
        blockData <- gets (flip (?!) blockLabel . blockMappings)
        let
            swap = M.lookup v (mappings blockData)
            defi = S.member v (defined blockData)
            unkn = M.lookup v (unknown blockData)
        if not defi && isNothing unkn then do   -- Niezdefiniowana w tym bloku
            -- Dodajemy do nieznanych
            newLoc <- newSSALocation
            let newVar = changeVariableLocation newLoc v
            let newData = blockData{unknown = M.insert v newVar (unknown blockData),
                                    mappings = M.insert v newVar (mappings blockData)}
            modify (updateBlockData blockLabel newData)
            return (Variable newVar)

        -- else if isNothing swap then do   -- Zdefiniowana i bez podmiany
        --                             -- <=> wstrzyknięty parametr
        --     newLoc <- newSSALocation
        --     let newVar = changeVariableLocation newLoc v
        --     let newData = blockData{mappings = M.insert v newVar (mappings blockData)}
        --     modify (updateBlockData blockLabel newData)
        --     return (Variable newVar)
        else do
            let Just var = swap
            return (Variable var)

    where updateBlockData label newData state =
            state{blockMappings = M.insert label newData (blockMappings state)}


transformFlowCtrl :: Label -> FlowCtrlOper -> SSATransformerM FlowCtrlOper
transformFlowCtrl blockLabel fctrl = case fctrl of
    (ConditionalFull a op b l1 l2) -> do
        new1 <- getRhsSSAOperand a blockLabel
        new2 <- getRhsSSAOperand b blockLabel
        return (ConditionalFull new1 op new2 l1 l2)

    (Return a) -> do
        new1 <- getRhsSSAOperand a blockLabel
        return (Return new1)

    _ -> return fctrl

-- Idziemy instrukcja po instrukcji zamieniając intrukcje na SSA
-- Jeżeli po lewej stronie pojawia się zmienna, jeszcze nie zdefiniowana
-- to możemy taką instrukcję pominąć. Dodajemy zmienną do zdefiniowanych.

-- Jeżeli po lewej stronie pojawia się zmienna już wcześniej zdefiniowana
-- tworzymy nową i zapamiętujemy podmianę, dalej jeżeli gdzieś
-- wykorzystywaliśmy zmienną poprzednią, teraz korzystamy z nowej

-- Jeżeli po prawej stronie pojawi się zmienna, której nie ma w bloku
-- dodajemy ją do 'nieznanych' i kontynuujemy. Jeżeli pojawi się zmienna
-- zauważona wcześniej używane jej ewentalnej podmiany.

nodeSSAT_1 :: CFGNode -> SSATransformerM CFGNode
nodeSSAT_1 node = do
    let nodeLabel = entryLabel node
    ssaCode <- transformCode nodeLabel (instructions node)
    return node{instructions = ssaCode}
    where
        transformCode label [] = return []
        transformCode label (instr:rest) = case instr of
            (FlowCtrlCode fctrl)     -> do
                newFctrl <- transformFlowCtrl label fctrl
                others <- transformCode label rest
                return (FlowCtrlCode newFctrl:others)

            (ValueCode op operation) -> do
                newOperation <- transformOperation label operation
                newOp <- getLhsSSAOperand False op label
                others <- transformCode label rest
                return ((newOp #= newOperation):others)

            (ReferenceCode op operation) -> do
                newOperation <- transformOperation label operation
                newOp <- getLhsSSAOperand True op label
                others <- transformCode label rest
                return ((newOp @= newOperation):others)

            _ -> willNeverHappen


        transformOperation label oper = do
            case oper of
                (Binary a binop b)  -> do
                    new1 <- getRhsSSAOperand a label
                    new2 <- getRhsSSAOperand b label
                    return (Binary new1 binop new2)

                (Unary unrop a)     -> do
                    new1 <- getRhsSSAOperand a label
                    return (Unary unrop new1)

                (LoadAddressFull a b o s)   -> do
                    new1 <- getRhsSSAOperand a label
                    new2 <- getRhsSSAOperand b label
                    return (LoadAddressFull new1 new2 o s)

                (LoadAddressArray a b o)    -> do
                    new1 <- getRhsSSAOperand a label
                    new2 <- getRhsSSAOperand b label
                    return (LoadAddressArray new1 new2 o)

                (LoadAddressOffset a o)     -> do
                    new1 <- getRhsSSAOperand a label
                    return (LoadAddressOffset new1 o)

                (LoadFrom a)    -> do
                    new1 <- getRhsSSAOperand a label
                    return (LoadFrom new1)

                (CopyOf a)      -> do
                    new1 <- getRhsSSAOperand a label
                    return (CopyOf new1)

                (Call callLabel operands)   -> do
                    news <- forM operands (flip getRhsSSAOperand label)
                    return (Call callLabel news)

                (CallReg a operands)  -> do
                    new1 <- getRhsSSAOperand a label
                    news <- forM operands (flip getRhsSSAOperand label)
                    return (CallReg new1 news)

                _   -> return oper


cfgSSAT_1 :: HasCallStack => FunType -> SSATransformerM ControlFlowGraph
cfgSSAT_1 ftype = do
    graph <- gets workingGraph
    let firstNode = entryNode graph
        label = entryLabel firstNode
    nodeData <- gets ((?! label) . blockMappings)
    index <- gets variableIndex

    -- let params = addParameterDefinitions 0 ftype nodeData
    --     (mapping, newIndex) = addDefaultMapping index params
    --     newBlockData = nodeData{defined = S.fromList params,
    --                             mappings = mapping}

    -- liftIO $ traceIO ("Entry mapping of " ++ label ++ ":\n" ++ show mapping)


    -- modify (\s -> s{blockMappings = M.insert label newBlockData (blockMappings s),
    --                 variableIndex = newIndex})

    cfgSSAT_1Traversal label


cfgSSAT_1Traversal :: HasCallStack => Label -> SSATransformerM ControlFlowGraph
cfgSSAT_1Traversal label = do
    visited <- gets visitedSet
    if S.member label visited then
        gets workingGraph
    else do
        let newS = S.insert label visited
        node <- gets ((?! label) .  workingGraph)
        let preds = S.toList $ entries node
            succ = S.toList $ exits node


        modify (\s -> s{visitedSet = newS})
        forM_ preds cfgSSAT_1Traversal

        newNode <- nodeSSAT_1 node
        modify (\s -> s{workingGraph = M.insert label newNode (workingGraph s)})

        forM_ succ cfgSSAT_1Traversal

        gets workingGraph


-- Uzupełniamy zmienne niewiadome w blokach poprzez dodanie funkcji phi
-- Dla każdej niewiadomej zmiennej w bloku, dostawiamy funkcję phi
-- Wartości funkcji phi ustalamy na podstawie poprzedników naszego bloku.
-- Poszukiwania idą rekurencyjnie w górę.


-- Jeżeli blok poprzedni posiada mapowanie szukanej wartości na zmienną, to
-- do funkcji phi wstawiamy zmapowaną zmienną.
-- Jeżeli blok poprzedni nie posiada mapowania szukanej zmiennej, to zmienna ta
-- jest nieużywana nigdzie w bloku. Dodajemy wtedy nową nieznaną zmienną do bloku
-- dla której będziemy szukali dalej funkcji phi.

cfgSSAT_2Traversal :: [Label] -> SSATransformerM ()
cfgSSAT_2Traversal [] = return ()
cfgSSAT_2Traversal (nLabel:rest) = do
    cfg <- gets workingGraph
    bmap <- gets blockMappings
    let nodeData = bmap ?! nLabel
        node = (?!) cfg nLabel
        predecessorsLabels = entries node
        successorsLabels = exits node
        unknownVariables = unknown nodeData

    if M.null (unknown nodeData) then do
        liftIO $ traceIO ("Every unknown variable of block " ++ nLabel ++ " has been found!")
        cfgSSAT_2Traversal rest
    else do

        -- mięso
        phiMappings <- forM (M.assocs unknownVariables) (\(oldVar, newVar) -> do

            varPhiMap <- forM (S.toList predecessorsLabels) (\pLabel -> do
                pNode <- gets ((?! pLabel) . workingGraph)
                pData <- gets ((?! pLabel) . blockMappings)
                let mapping = M.lookup oldVar (mappings pData)
                predVariable <- if isNothing mapping then do
                    liftIO $ traceIO ("Lifting unknown " ++ show oldVar ++ " to " ++ (entryLabel pNode))
                    -- Blok nie posiada mapowania tej zmiennej, musimy ją dodać
                    -- newLoc <- newSSALocation
                    -- let newVar = changeVariableLocation newLoc oldVar
                    let newpData = pData{unknown = M.insert oldVar newVar (unknown pData)}
                    modify $ updateBlockData (entryLabel pNode) newpData
                    return newVar

                else do
                    let Just var = mapping
                    return var

                -- (skąd, zmienna)
                return (entryLabel pNode, predVariable)
                )
            -- (nowa zmienna, mapowanie phi)
            return (oldVar, newVar, varPhiMap)
            )
        let newMappings = map (\(oldVar, newVar, _) -> (oldVar, newVar)) phiMappings

        phiInstructions <- forM phiMappings (\(_, var, mapping)->
                let operands = map (second Variable) mapping in
                    return (PhiFunction (Variable var) operands)
            )
        -- Dodajemy nowe funkcje phi
        let newCode = phiInstructions ++ instructions node
            newNode = node{instructions = newCode}
            newNodeData = nodeData{unknown = M.empty,
                                   mappings = M.union (mappings nodeData)
                                                      (M.fromList newMappings)}

        modify (updateBlockNode nLabel newNode)
        modify (updateBlockData nLabel newNodeData)
        cfgSSAT_2Traversal (S.toList predecessorsLabels ++ S.toList successorsLabels ++ rest)

        where updateBlockData label newData state =
                state{blockMappings = M.insert label newData (blockMappings state)}

              updateBlockNode label newNode state =
                state{workingGraph = M.insert label newNode (workingGraph state)}





cfgSSAT_2 :: SSATransformerM ()
cfgSSAT_2 = do
    (cfgSSAT_2Traversal . M.keys) =<< gets workingGraph
    repeatUntillConvergence 10
    where
        repeatUntillConvergence 0 = return ()
        repeatUntillConvergence i = do
            bmap <- gets blockMappings
            unless (all (null . unknown) bmap) $ do
                (cfgSSAT_2Traversal . M.keys) =<< gets workingGraph
                repeatUntillConvergence (i-1)



-- Usuwamy niepotrzebne funkcje phi. Rozpoczynamy propagację trywialnych funkcji
-- phi od góry i propagujemy w dół. Przerywamy, kiedy nie naniesiemy już żadnych
-- zmian.


allEqual :: Eq a => [a] -> Bool
allEqual []   = True
allEqual [x]  = True
allEqual (x:y:rest) = (x == y) && allEqual (y:rest)

isTrivialPhiFunction :: (Operand, [(Label, Operand)]) -> Bool
isTrivialPhiFunction (_, mapping) =
    let operands = map snd mapping in
        allEqual operands




baseUpdateOperand f oper = case oper of
    (Binary a binop b)          -> Binary (f a) binop (f b)
    (Unary unrop a)             -> Unary unrop (f a)
    (LoadAddressFull a b o s)   -> LoadAddressFull (f a) (f b) o s
    (LoadAddressArray a b o)    -> LoadAddressArray (f a) (f b) o
    (LoadAddressOffset a o)     -> LoadAddressOffset (f a) o
    (LoadFrom a)    -> LoadFrom (f a)
    (CopyOf a)      -> CopyOf (f a)
    (Call callLabel operands) -> Call callLabel (map f operands)
    (CallReg a operands)  -> CallReg (f a) (map f operands)
    _   -> oper

updateOperation :: (Operand -> Operand) -> QuadCode -> QuadCode
updateOperation f (FlowCtrlCode fctrl) = FlowCtrlCode $ case fctrl of
    (ConditionalFull a op b l1 l2)  ->
        ConditionalFull (f a) op (f b) l1 l2
    (Return op) -> Return (f op)
    _ -> fctrl
updateOperation f (ValueCode op oper) = f op #= baseUpdateOperand f oper
updateOperation f (ReferenceCode op oper) = f op @= baseUpdateOperand f oper
updateOperation f (PhiFunction op mapping) =
    PhiFunction (f op) (map (second f) mapping)

variableSubstitution :: [(Operand,Operand)] -> VariableMapping
variableSubstitution pairs =
    let forwardMap = M.fromList pairs
        backwardMap = M.fromList (map swap pairs)
    in
        if null pairs then Vmap True id id
        else Vmap False (f forwardMap) (f backwardMap)

    where f mapp op = case op of
                (Variable var) -> M.findWithDefault (Variable var) op mapp
                _   -> op


data VariableMapping = Vmap {
    isIdentity :: Bool,
    forward :: Operand -> Operand,
    backward :: Operand -> Operand
}

-- cfgSSAT_3Traversal'' :: Set Label -> VariableMapping -> Label -> SSATransformerM (Set Label)
-- cfgSSAT_3Traversal'' visited mapping nLabel =  
--     if S.member nLabel visited then return visited
--     else do

--     let newVisited = S.insert nLabel visited

--     unless (isIdentity mapping) $ do
--         let formap = forward mapping
--         debugTrace 0 ("T3 up " ++ nLabel)

--         -- Aktualizujemy nasz kod
--         node <- gets ((?! nLabel) . workingGraph)
--         newCode <- forM (instructions node) (\c -> do
--                     let x = updateOperation formap c
--                     -- when (x /= c) $
--                     debugTrace 0 (show c ++ " ->\n\t" ++ show x)
--                     return x
--                 )

--         when (newCode /= (instructions node)) $ do
--                 debugTrace 3 ("Substituting code of " ++ nLabel ++ "\n")
--                 modify (updateBlockNode nLabel node{instructions = newCode})

--     -- Sprawdzamy nasze !nowe! podstawienie
--     node <- gets ((?! nLabel) . workingGraph)
--     let (phiFuncs, restInstr) = getPhiInfo (instructions node) []
--         substitutions = M.fromList $
--                         map (swap . second (snd . head)) $
--                         filter isSubstitutionPhi phiFuncs
--         reverseSubs = M.fromList $
--                       map (second (snd . head)) $
--                       filter isSubstitutionPhi phiFuncs

--         complexPhis   = filter (not . isSubstitutionPhi) phiFuncs

--         myMapping = variableSubstitution substitutions
--         revMyMapping = variableSubstitution reverseSubs

--     predecessor <- gets (entries . (?! nLabel) . workingGraph)
--     successors <- gets (exits . (?! nLabel) . workingGraph)

--     debugTrace 3 ("Mapping from " ++ nLabel ++ ":\n" ++ unlines (map show $ M.toList substitutions))

--     when (isJust myMapping) $ do
--         let Just mapping = myMapping
--             Just revmapping = revMyMapping
--         newCode <- forM (instructions node) (\c -> do
--                     let x = updateOperation mapping c
--                     when (x /= c) $
--                         debugTrace 0 (show c ++ " ->\n\t" ++ show x)
--                     return x
--                 )

--         when (newCode /= (instructions node)) $ do
--                 debugTrace 3 ("Substituting code of " ++ nLabel ++ "\n")
--                 modify (updateBlockNode nLabel node{instructions = newCode})
--                 forM_ successors (cfgSSAT_3Traversal_Down S.empty revmapping)


--     forM_ predecessor (cfgSSAT_3Traversal'' myMapping)


--     where
--         updateBlockNode label newNode state =
--             state{workingGraph = M.insert label newNode (workingGraph state)}

--         getPhiInfo [] funcs = (funcs, [])
--         getPhiInfo ((PhiFunction op mapping):rest) acc =
--             getPhiInfo rest ((op, mapping):acc)
--         getPhiInfo r@(_:rest) acc = (acc, r)

--         isSubstitutionPhi (op, mapping) =
--             not (null mapping) && allEqual (map snd mapping) && op /= snd (head mapping)


-- Wziąć podstawienie
-- Rozpocząć propagację wzdłóż przepływu:
-- Każdy węzeł i zmiana osobno

cfgSSAT_3Traversal_Down :: Set Label -> (Operand -> Operand) -> Label -> SSATransformerM (Set Label)
cfgSSAT_3Traversal_Down visited mapping nLabel = do
    if S.member nLabel visited then
        return visited
    else do
        debugTrace 0 ("T3 down " ++ nLabel)
        let newVisited = S.insert nLabel visited
        cfg <- gets workingGraph
        bmap <- gets blockMappings

        let nodeData = bmap ?! nLabel
            node = (?!) cfg nLabel
            successorsLabels = exits node


        -- Aktualizujemy nasz kod
        newCode <- forM (instructions node) (\c -> do
                    let x = updateOperation mapping c
                    when (x /= c) $
                        debugTrace 0 (show c ++ " ->\n\t" ++ show x)
                    return x
                    -- foldM (\c mapping -> do    -- przykładamy w kolejności
                    --     liftIO $ traceIO ("Modyfing code of " ++ show nLabel)
                    --     let x = updateOperation mapping c
                    --     liftIO $ traceIO (show c ++ " ->\n\t" ++ show x)
                    --     return x
                    --     ) c mappings
                )

        when (newCode /= (instructions node)) $ do
            debugTrace 3 ("Substituting code of " ++ nLabel ++ "\n")
            modify (updateBlockNode nLabel node{instructions = newCode})

        -- Jeżeli zmieniła się prawa strona funkcji phi, musimy to
        -- spropagować w górę!

        -- Propagujemy zmiany dalej
        foldM (\vis label -> do
            cfgSSAT_3Traversal_Down vis mapping label
            ) newVisited successorsLabels 

        
        -- -- Patrzymy czy my, mamy jeszcze coś do podstawienia
        -- node <- gets ((?! nLabel) . workingGraph)   -- pobieramy nowy węzeł
        -- let (phiFuncs, restInstr) = getPhiInfo (instructions node) []

        --     substitutions = M.mapMaybe id $ M.fromList $
        --                     map (second (fmap (fst . swap) . listToMaybe)) $
        --                     filter isSubstitutionPhi phiFuncs
        --     complexPhis   = filter (not . isSubstitutionPhi) phiFuncs

        --     myMapping = variableSubstitution substitutions

        -- unless (null substitutions) $ do
        --     debugTrace 0 ("New substitutions from " ++ nLabel ++" :\n" ++ unlines (map show (M.assocs substitutions)))
        --     -- Mamy coś do przekazania
        --     cfgSSAT_3Traversal' S.empty myMapping nLabel
        

        





    where
        getPhiInfo [] funcs = (funcs, [])
        getPhiInfo ((PhiFunction op mapping):rest) acc =
            getPhiInfo rest ((op, mapping):acc)
        getPhiInfo r@(_:rest) acc = (acc, r)

        isSubstitutionPhi (op, mapping) =
            not (null mapping) && allEqual (map snd mapping) && op /= snd (head mapping)

        updateBlockData label newData state =
            state{blockMappings = M.insert label newData (blockMappings state)}

        updateBlockNode label newNode state =
            state{workingGraph = M.insert label newNode (workingGraph state)}

cfgSSAT_3 :: SSATransformerM ControlFlowGraph
cfgSSAT_3 = do
    graph <- gets workingGraph
    liftIO $ traceIO ("SSA CFG przed eliminacją phi:\n")
    liftIO (cfgShowCodeHuman graph)

    let startingNode = entryNode graph
        startingLabel = entryLabel startingNode

    let endingNode = (@!) (M.elems (M.filter (null . exits) graph))
        endingLabel = entryLabel endingNode

    let (initMapping, nullness) = (calcMapping endingNode)
    -- cfgSSAT_3Traversal'' nullness initMapping endingLabel
    traverseBFS (neighbors graph) action S.empty startingLabel

    graph <- gets workingGraph
    liftIO $ traceIO ("SSA CFG po eliminacji phi:\n")
    liftIO (cfgShowCodeHuman graph)

    -- x <- cfgSSAT_3Traversal (map entryLabel sortedNodes)

    -- graph <- gets workingGraph
    -- liftIO $ traceIO ("SSA CFG po eliminacji phi:\n"
    --     ++ unlines (cfgShowCodeHuman graph))

    return graph
    where
        neighbors cfg nodeLabel = S.toList (exits (cfg ?! nodeLabel))
        action nodeLabel = do
            node <- gets ((?! nodeLabel) . workingGraph)
            let (phiFuncs, restInstr) = getPhiInfo (instructions node) []
                substitutions = map (second (snd . head)) $
                                filter isSubstitutionPhi phiFuncs
                complexPhis   = filter (not . isSubstitutionPhi) phiFuncs

                myMapping = variableSubstitution substitutions
            if null substitutions then return S.empty
            else 
                cfgSSAT_3Traversal_Down S.empty (forward myMapping) nodeLabel

        calcMapping node =
            let (phiFuncs, restInstr) = getPhiInfo (instructions node) []
                substitutions =  map (second (snd . head)) $
                                filter isSubstitutionPhi phiFuncs
                complexPhis   = filter (not . isSubstitutionPhi) phiFuncs
            in
                (variableSubstitution substitutions, null substitutions)

        getPhiInfo [] funcs = (funcs, [])
        getPhiInfo ((PhiFunction op mapping):rest) acc =
            getPhiInfo rest ((op, mapping):acc)
        getPhiInfo r@(_:rest) acc = (acc, r)

        isSubstitutionPhi (op, mapping) =
            not (null mapping) && allEqual (map snd mapping) && op /= snd (head mapping)



traverseBFS neighbors action visited n =
    if S.member n visited then return ()
    else do
        let newVisited = S.insert n visited
        action n
        forM_ (neighbors n) (\new -> do
            traverseBFS neighbors action newVisited new
            )


