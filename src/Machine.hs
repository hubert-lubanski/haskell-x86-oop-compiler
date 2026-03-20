{-# LANGUAGE LambdaCase #-}

-- This was edited by LTSP client - poggies!

module Machine where
import Common
import Prelude hiding (LE, LT, GE, GT, NE, EQ)
import Types hiding (generatedCode)
import Intermediate

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import qualified Data.List as L

import qualified SSATransformation as SSA
import Control.Monad.State
import Control.Monad
import Error (waltIDontKnowMan, willNeverHappen, Err (Err), printCodeFragment)
import GHC.Stack (HasCallStack)
import Grammar.Par
import Grammar.Abs hiding (Div, Mod, LE, LT, GE, GT, NE, EQ)

import Data.Maybe (fromMaybe, isJust, isNothing)
import SSATransformation (runCFGGenerator, makeCFG, transformToSSA, allEqual)
import System.Exit (exitFailure)
import Debug.Trace (traceIO, trace)
import System.Process (waitForProcess)
import Data.Bifunctor (Bifunctor(second, first, bimap))
import Data.Tuple (swap)
import GHC.Base (Any)
import Data.List (sortBy, sortOn)
import Debugging
import Data.Either (isLeft)



setElemAt :: HasCallStack => Int -> Set a -> a
setElemAt which set = if which < 0 || S.size set <= which then setError
                      else S.elemAt which set
    where setError = error ("Index (" ++ show which ++ ") is not in set")
liveEmit = True



__prettyPrintRegisters = (unlines . map show .  M.elems)
__prettyPrintVariables vars =
        (unlines . map (\(v,l) ->
                   show v ++ " in " ++ (show . S.toList) l) . M.assocs) vars

type AliveAtCode = [(QuadCode, Set Variable)]

type ControlFlowGraph = Map Label CFGNode
data CFGNode = CFGNode {
    position :: Integer,
    entryLabel :: Label,
    instructions :: AliveAtCode,

    entries :: Set Label,
    exits   :: Set Label,

    aliveEnd   :: Set Variable,
    aliveEntry :: Set Variable,

    entryRegisterBind :: Map Variable Register
}


newtype LivenessCalculatorState = LCState {
    workingGraph :: ControlFlowGraph
}

emptyLCState = LCState M.empty

type LivenessCalculatorM a = StateT LivenessCalculatorState IO a


_calcLiveness :: Set Variable -> QuadCode -> Set Variable
_calcLiveness out instr = case instr of
    -- kill: op
    (ValueCode op oper) -> processOperation oper (deleteVar op out)
    -- kill: -
    (ReferenceCode op oper) -> processOperation oper (insertVar op out)
    (FlowCtrlCode fctrl) -> case fctrl of
        (ConditionalFull a c b l1 l2) -> insertVar2 a b out
        (Return a)  -> insertVar a out
        _ -> out
    _ -> out
    where
        processOperation oper newOut =  case oper of
            (Binary a oper b)   -> insertVar a (insertVar b newOut) -- use: a, b
            (Unary oper a)      -> insertVar a newOut -- use: a
            (LoadAddressFull a i _ _)   -> insertVar2 a i newOut -- use: a, i
            (LoadAddressArray a i _)    -> insertVar2 a i newOut -- use: a,i
            (LoadAddressOffset a _)     -> insertVar a newOut -- use: a
            (LoadFrom a)                -> insertVar a newOut
            (CopyOf a)                  -> insertVar a newOut
            (Call _ as)     -> foldr insertVar newOut as
            (CallReg a as)  -> insertVar a (foldr insertVar newOut as)
            _ -> newOut

        insertVar op set = case op of
            (Variable var) -> S.insert var set
            _   -> set
        insertVar2 op1 op2 set = insertVar op2 (insertVar op1 set)
        deleteVar op set = case op of
            (Variable var) -> S.delete var set
            _ -> set

calcLiveness :: SSA.ControlFlowGraph -> IO ControlFlowGraph
calcLiveness ssacfg =
    evalStateT (do
            calcAliveFromSSA ssacfg
            gets workingGraph
        ) emptyLCState


calcAliveFromSSA :: SSA.ControlFlowGraph -> LivenessCalculatorM ()
calcAliveFromSSA cfg = do
    nodeAliveAtEnd <- mapM (translateNodeFromSSA cfg) cfg
    let x = M.mapWithKey (\k aliveAtTheEnd ->
            let node = cfg ?! k
                revCode = reverse . SSA.instructions $ node
                (aliveAtTheEntry, annotatedCode) = calcAliveAt aliveAtTheEnd revCode []
            in
                CFGNode (SSA.position node) k annotatedCode
                        (SSA.entries node) (SSA.exits node)
                        aliveAtTheEnd aliveAtTheEntry M.empty
            ) nodeAliveAtEnd
        phiEliminated = M.map eliminateRedundantPhis x

    modify (\s -> s{workingGraph = phiEliminated})


calcAliveAt out [] acc = (out, acc)
calcAliveAt out (instr:rest) acc =
    let aliveNow = _calcLiveness out instr
    in
        calcAliveAt aliveNow rest ((instr, out):acc)

translateNodeFromSSA :: SSA.ControlFlowGraph ->  SSA.CFGNode ->
                    LivenessCalculatorM (Set Variable)
translateNodeFromSSA cfg node = do
    let ancestors = S.toList (SSA.exits node)
        nodeLabel = SSA.entryLabel node

    S.fromList . concat <$> forM ancestors (\label -> do
        let ancsNode = cfg ?! label
            ancsCode = SSA.instructions ancsNode

        return $ map getVariable
               $ filter isVariable
               $ map snd
               $ filter ((nodeLabel ==) . fst)
               $ concat (getPhiInfo ancsCode [])

        )

    where
        getPhiInfo [] funcs = funcs
        getPhiInfo ((PhiFunction op mapping):rest) acc =
            getPhiInfo rest (mapping:acc)
        getPhiInfo r@(_:rest) acc = acc

        getVariable (Variable var) = var
        getVariable _ = willNeverHappen


eliminateRedundantPhis :: CFGNode -> CFGNode
eliminateRedundantPhis node =
    let (phis, restCode) = getPhiInfo (instructions node) []
        nonTrivalPhis =  filter (not . isTrivialPhiFunction . fst) phis
    in
        node{instructions = nonTrivalPhis ++ restCode}
    where
        getPhiInfo [] acc = (acc, [])
        getPhiInfo (phi@(PhiFunction op mapping, alive):rest) acc =
            getPhiInfo rest (phi:acc)
        getPhiInfo r@(_:rest) acc = (acc, r)

        isTrivialPhiFunction (PhiFunction op mapping) =
            let operands = map snd mapping in
                allEqual operands



maximalRegisterNumber = 14

indexList :: Num t => t -> [b] -> [(t, b)]
indexList _ [] = []
indexList i (x:xs) = (i,x):indexList (i+1) xs

x86_64registers =["rax", "rsi", "rdi", "rcx", "r8", "r9", "r10", "r11" ,
                  "rdx", "rbx", "r12", "r13", "r14", "r15",
                  "rsp", "rbp"] --special

x86_64VolatileRegisters = ["rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"]
x86_64PreservedRegisters = ["rbx", "r12", "r13", "r14", "r15"]
x86_64ABIMaxRegisters = 6
x86_64ABIregisters = ["rdi", "rsi", "rdx", "rcx", "r8", "r9", "how about no"]
rax = registerNumber "rax"
rdx = registerNumber "rdx"
r8  = registerNumber "r8"

isRegister :: VariableLocation -> Bool
isRegister (Reg _) = True
isRegister _ = False

extractRegister :: HasCallStack => VariableLocation -> Register
extractRegister (Reg r) = r
extractRegister _ = waltIDontKnowMan

isOnStack :: VariableLocation -> Bool
isOnStack (Mem _) = True
isOnStack _ = False

extractOnStack :: HasCallStack => VariableLocation -> Int
extractOnStack (Mem o) = o
extractOnStack _ = waltIDontKnowMan


registerNumber :: HasCallStack => String -> Int
registerNumber regstr = fromMaybe waltIDontKnowMan (L.elemIndex regstr x86_64registers)



data MachineLocation    = AddressLabel Label
                        | StackOffset Int
                        | InRegister Int
                        | ImmediateInt Int
                        | Address MachineLocation                   -- base
                                  (Maybe (MachineLocation, Int))    -- array
                                  (Maybe MachineLocation)           -- offset
                        | ToLabel Label
    deriving (Eq)

addressRegister :: Int -> MachineLocation
addressRegister i = Address (InRegister i) Nothing Nothing

addressImmediate i = Address (ImmediateInt i) Nothing Nothing

instance Show MachineLocation where
    show (Address loc1 mloc2 mloc3) =
        let part2 = if isNothing mloc2 then ""
                    else let Just (loc, mult) = mloc2 in
                        (" + " ++ show loc ++ " * " ++ show mult)
            part3 = if isNothing mloc3 then ""
                    else let Just loc = mloc3 in
                        (" + " ++ show loc)
        in
            concat ["QWORD [", show loc1, part2, part3, "]"]

    show (StackOffset o)     = "QWORD [rbp -" ++ show (o * 8) ++ "]"
    show (InRegister r)      = x86_64registers!!r
    show (ImmediateInt i)    = show i
    show (ToLabel l)         = l
    show (AddressLabel l)    = "QWORD [rel "++ l ++ "]"


data MachineCode    = Instruction0 String
                    | Instruction1 String MachineLocation
                    | Instruction2 String MachineLocation MachineLocation
                    | ToResolve String
                    | Optional MachineCode
                    | InstructionComment MachineCode String
                    | Comment String
    deriving (Eq)

instance Show MachineCode where
    show (Instruction0 str) = str
    show (Instruction1 str ml) = str ++ " " ++ show ml
    show (Instruction2 str ml1 ml2) = str ++ " " ++ show ml1 ++ ", " ++ show ml2
    show (ToResolve s) = "%ResolveMe<" ++ show s ++ ">%\n"
    show (Optional mc) = show mc ++ " \t; optional\n"
    show (InstructionComment i c) =  appendAt 40 (show i) (" \t; " ++ c)
    show (Comment c) = "; " ++ c


type Register = Int

type Offset = Int

data VariableLocation = Reg Int | Mem Offset | Imm Int
    deriving (Eq)

instance Ord VariableLocation where
  (<=) (Reg _) (Mem _) = True
  (<=) (Reg _) (Imm _) = True
  (<=) (Mem _) (Reg _) = False
  (<=) (Reg i) (Reg j) = i <= j
  (<=) (Mem i) (Mem j) = i <= j
  (<=) (Mem _) (Imm _) = False
  (<=) (Imm i) (Imm j) = i <= j

instance Show VariableLocation where
    show (Reg i) =  x86_64registers!!i -- "R" ++ show i -- NOTE
    show (Mem o) = "QWORD [rbp - " ++ show (o * 8) ++ "]"
    show (Imm i) = show i

asMachine :: VariableLocation -> MachineLocation
asMachine (Reg i) = InRegister i
asMachine (Imm i) = ImmediateInt i
asMachine (Mem o) = StackOffset o

asAddress :: VariableLocation -> MachineLocation
asAddress (Reg i) = addressRegister i
asAddress (Imm i) = addressImmediate i
asAddress (Mem o) = willNeverHappen

instr2 :: String -> VariableLocation -> VariableLocation -> MachineCode
instr2 inst vl1 vl2 = Instruction2 inst (asMachine vl1) (asMachine vl2)

instr1 :: String -> VariableLocation -> MachineCode
instr1 inst vl = Instruction1 inst (asMachine vl)
data RegisterState = Free | Occupied | Reserved
    deriving (Eq, Ord, Show)

data RegisterDescription = RegDesc {
    number :: Int,
    regstate :: RegisterState,
    contents :: Set Variable
}

instance Show RegisterDescription where
    show (RegDesc i s c) =
        "["++ show i ++ "]" ++show (Reg i) ++ " " ++ if s == Free then
                            " *free* "
                        else
                            show (S.toList c)


type RegisterDescriptionMap = Map Int RegisterDescription
type VariableDescriptionMap = Map Variable (Set VariableLocation)
-- Generacja dla grafu pojedynczej funkcji
data MachineCodeGeneratorState = MCGState {
    flowGraph :: ControlFlowGraph,
    registerUsage :: RegisterDescriptionMap,
    variableDescr :: VariableDescriptionMap,
    generatedCode :: Map Label [MachineCode],

    initialNodeState :: Map Label (RegisterDescriptionMap,
                                   VariableDescriptionMap),

    nodeEndDescriptons :: Map Label (RegisterDescriptionMap,
                                    VariableDescriptionMap),
    currentNode :: Label,
    currentCode :: AliveAtCode,
    aliveBeforeCurrentInst :: Set Variable,

    unusedMemory :: Set Int,

    maximalOffset :: Int,
    usedRegisters :: Set Int
}

emptyMCGState :: ControlFlowGraph -> MachineCodeGeneratorState
emptyMCGState cfg  = MCGState {
    flowGraph = cfg,
    registerUsage = allRegistersFree,
    variableDescr = M.empty,
    generatedCode = M.empty,
    initialNodeState = M.empty,

    nodeEndDescriptons = M.empty,

    currentNode = "",
    currentCode = [],
    aliveBeforeCurrentInst = S.empty,

    unusedMemory = S.empty,

    maximalOffset = 0,
    usedRegisters = S.empty
}

allRegistersFree :: Map Int RegisterDescription
allRegistersFree = M.fromList $ map (\i -> (i,freeRegister i)) (take maximalRegisterNumber [0..])
    where freeRegister i = RegDesc i Free S.empty

type MachineCodeGeneratorM a = StateT MachineCodeGeneratorState IO a

emit :: HasCallStack => MachineCode -> MachineCodeGeneratorM ()
emit mc = do
    let
    when liveEmit $ (liftIO . traceIO) (altredColor "emit:  " ++ show mc)
    label <- gets currentNode
    code <-  gets ((?! label) . generatedCode)
    let newCode = mc:code
    modify (\s -> s{generatedCode = M.insert label newCode (generatedCode s)})


cyclicMove :: Register -> Variable -> Map Variable (Set VariableLocation)
           -> Map VariableLocation (Set Variable)
           -> MachineCodeGeneratorM (Map Variable (Set VariableLocation))
cyclicMove swapper varInside varsToMove loc2varMap = do
    -- NOTE przed wejściem zakładamy, że zmienna varInside nie ma
    -- swojej na liście swoich lokalizacji rejestru swapRegister.
    let swapRegister = Reg swapper
    -- Mamy zmienną varInside w rejestrze swapRegister
    -- Patrzymy, gdzie chce ona się znaleźć:
    --  Sotrujemy po lokalizacjach 'wolnych'
    -- Jeżeli lokalizacja jest wolna, to dokonujemy 'mov' i możemy powtarzać
    -- Jeżeli lokalizacja jest zajęta, to dokonujemy 'xchg' i odpalamy się
    -- dla nowej zmiennej
    -- Musimy odnotowywać:
    --  nowe położenia zmiennych
    let maybeVarLocs = M.lookup varInside varsToMove
    if isNothing maybeVarLocs then
        -- Ta zmienna nie wymaga przenoszenia
        return varsToMove
    else let Just varLocs = maybeVarLocs in do

        -- let needMovingLocs = discardAlreadyPresentPlaces varInside varLocs

        -- Zmienna może być oczekiwana w wielu miejscach
        -- Początkowo przenosimy ją do wszystkich wolnych miejsc
        locsLeft <- moveToFreePlaces varInside swapRegister varLocs

        if S.null locsLeft then
            -- Nie ma pozostałych miejsc.
            -- Usuwamy zmienną z mapy do przeniesienia.
            return $ M.delete varInside varsToMove
        else do
            -- Pozostały tylko nietrywialne miejsca
            let (swapNow, swapsLeft) = S.splitAt 1 locsLeft
                swapLoc = setElemAt 0 swapNow

                newVarsToMove = if S.null swapsLeft then
                                    -- nic nie zostanie, więc usuwamy tą zmienną
                                    M.delete varInside varsToMove
                                else
                                    -- pozostałe miejsca
                                    M.insert varInside swapsLeft varsToMove

            let variablesAtSwapLoc = loc2varMap ?! swapLoc
            let swappedVar = setElemAt 0 variablesAtSwapLoc
            debugTrace 2 ("Swapping " ++ show varInside ++ "'s location with " ++ show swappedVar)

            -- NOTE Nigdy nie wybieramy rejestru, w którym już jest dobra
            -- zmienna!
            emit $ instr2 "xchg" swapLoc swapRegister

            -- Aktualizujemy pozycje zmiennych
            addVariableLocation varInside swapLoc
            removeVariableLocation swappedVar swapRegister

            -- TODO poniższa optymalizacja
            -- let swappedVarLocs = M.findWithDefault S.empty swappedVar
            --                                                newVarsToMove
            --     newSwappedLocs = S.delete swapRegister swappedVarLocs


            -- if S.member swapRegister swappedVarLocs then do
            --     -- Nie możemy kontynuować. Podmieniona zmienna powinna być
            --     -- w swapRegister.

            --     let evenNewVarsToMove = 
            --             if S.null newSwappedLocs then
            --                 M.delete swappedVar newVarsToMove
            --             else
            --                 M.insert swappedVar newSwappedLocs newVarsToMove
            --     debugTrace 2 ("Przerywamy cyclicMove dla " ++ show swappedVar)
            --     return (evenNewVarsToMove, Nothing)
            -- else do

            debugTrace 2 ("Kontynuujemy cyclicMove dla " ++ show swappedVar)
            cyclicMove swapper swappedVar newVarsToMove loc2varMap

    where
        discardAlreadyPresentPlaces var whereLocs =
            let isAlreadyThere loc =
                    S.member var $ M.findWithDefault S.empty loc loc2varMap
            in
                S.filter isAlreadyThere whereLocs

        moveToFreePlaces var swapRegister whereLocs = do
            let freeLocs = S.filter (`M.notMember` loc2varMap) whereLocs

            forM_ freeLocs (\loc -> do
                emit $ instr2 "mov" loc swapRegister
                )

            -- Zapisujemy nowe położenia zmiennej (do stanu)
            appendVariableLocations var freeLocs

            return (S.difference whereLocs freeLocs)

        appendVariableLocations var addition = do
            currentLocs <- gets ((?! var) . variableDescr)
            let newLocs = S.union addition currentLocs
            modify (\s -> s{variableDescr = M.insert var newLocs (variableDescr s)})

        removeVarLocFrom var vl mapp =
            let varDesc = S.delete vl (mapp ?! var) in
            M.insert var varDesc mapp


unifyEndState :: HasCallStack => MachineCodeGeneratorM ()
unifyEndState = do
    label <- gets currentNode
    node  <- gets ((?! label) . flowGraph)
    regUse <- gets registerUsage
    varUse <- gets variableDescr

    requiredState <- gets (M.lookup label . nodeEndDescriptons)
    if isNothing requiredState then
        return ()
    else do
        let Just (reqRegs, reqVars) = requiredState
        -- Algorytm nie jest wyrafinowany:
        {-  1. Sprawdź, które zmienne są już na miejscu i o nich zapomnij
            2. Weź wolny rejestr R.
                Jeżeli wszystkie są zajęte zmiennymi: push R, ..., pop R
            3. Powtarzaj, dopóki są niepasujące zmienne:
                .1 Weź niepasującą zmienną
                .2 Załaduj do R
                .3 Jeżeli w docelowym miejscu jest inna niepasująca zmienna:
                    xchg R, A -> powtórz krok .3 dla nowej zmiennej
                   Jeżeli docelowe miejsce jest puste, idź do podpunktu 3
        -}


        debugTrace 3 ("Aktualny stan zmiennych:\n" ++ __prettyPrintVariables varUse)
        debugTrace 3 ("Wymagany stan zmiennych:\n" ++ __prettyPrintVariables reqVars)

        debugTrace 2 ("Akutalny stan rejestrów:\n" ++ __prettyPrintRegisters regUse)

        -- NOTE pamiętać o powtórzeniach zmiennych

        -- Obcinamy tylko do zmiennych w wymaganym stanie
        let unrelevantVars = M.difference varUse reqVars


        forM_ (M.keys unrelevantVars) freeVariable

        relevantVars <- gets variableDescr

        -- Tworzymy odwzorowanie odwrotne Lokacja -> Set Zmienna, gdzie lokacja
        -- należy do akutalnych położeń zmiennych
        let loc2varMap = invertMap relevantVars
        debugTrace 4 ("Odwzorowanie odwrotne:\n" ++ __prettyPrintVariables loc2varMap)

        let varsToMove = M.mapMaybeWithKey (\v currLocs ->
                let reqLocs = reqVars ?! v
                    -- Wymagane \ aktualne = do przeniesienia
                    neededLocs = S.difference reqLocs currLocs
                in
                    if S.null neededLocs then
                        Nothing
                    else
                        Just neededLocs
                ) relevantVars

        debugTrace 4 ("Zmienne wymagające przeniesienia:\n" ++ __prettyPrintVariables varsToMove)

        if M.null varsToMove then return ()
        else do
            -- TODO optymalizacja - weźmy zmienną, która już jest w rejestrze!

            maybeReg <- tryFreeRegisterOtherThan (M.keys (M.filter ((/= Free) . regstate)  reqRegs))
            if isNothing maybeReg then do
                let sreg = "r11"
                    specialRegisterNumber = registerNumber sreg
                    specialRegister = Reg specialRegisterNumber

                    varsInSR = M.findWithDefault S.empty specialRegister loc2varMap
                    (reqVarsToSR, otherReqVars) =
                        M.partition (S.member specialRegister) varsToMove

                    restToMove = M.intersection varsToMove reqVarsToSR

                emit $ Comment "; --Unifikacja międzyblokowa-- ;"
                forM_ (M.elems varsToMove) (\setvl -> do
                    forM_ setvl (\case
                            (Mem o) -> modify (\s -> s{unusedMemory = S.delete o (unusedMemory s)})
                            _ -> return ()
                        )
                    )
                -- odsyłamy rejestr do pamięci
                savedAt <- saveRegisterToMemory specialRegisterNumber
                -- Zmieniamy aktualne mapowanie z SR na pamięć oraz
                -- poprzednio docelowe miejsce z SR na pamięć
                let newloc2varMap =
                        if not (S.null varsInSR) then
                            M.insert savedAt varsInSR (M.delete specialRegister loc2varMap)
                        else M.delete specialRegister loc2varMap
                    varsToPrevSR  = M.map (S.insert savedAt . S.delete specialRegister) reqVarsToSR
                    newVarsToMove = M.union varsToPrevSR otherReqVars

                -- używamy SR do sprowadzenia pozostałych zmiennych
                debugTrace 0 ("Wymagany stan (z R11):\n" ++ show varsToMove)
                debugTrace 0 ("Wymagany stan (bez R11):\n" ++ show newVarsToMove)
                debugTrace 0 ("Mapowanie odwrotne: " ++ show newloc2varMap)
                moveAllVariables specialRegisterNumber newloc2varMap newVarsToMove
                -- Teraz wiemy, że wszystkie zmienne, które chciały być w SR
                -- są w pamięci

                emit $ instr2 "mov" specialRegister savedAt

            else do
                let Just swapper = maybeReg
                emit $ Comment "; --Unifikacja międzyblokowa-- ;"
                debugTrace 1 "Moving variables around"
                debugTrace 0 ("Mapowanie odwrotne: " ++ show loc2varMap)
                moveAllVariables swapper loc2varMap varsToMove
                debugTrace 1 "All done"

    where
        moveAllVariables swapper loc2varMap varsToMove =
            unless (M.null varsToMove) $ do
                let firstVar = fst $ M.elemAt 0 varsToMove
                debugTrace 2 ("Starting cycle of " ++ show firstVar)

                -- TODO Mini optymalizacja:
                -- Pojedyncze przemieszczenia robimy od razu

                varLoc <- getBestVariableLocation firstVar
                emit $ instr2 "mov" (Reg swapper) varLoc

                cyclicMove swapper firstVar varsToMove loc2varMap >>=
                    moveAllVariables swapper loc2varMap



        calcRegistersState variablesMap =
            M.fromList  $ map ((\(i,v) -> (i, makeRegister i v))
                        . swap . second getRegisterNumber)
                        $ filter (isRegister . snd)
                        $ map (second $ setElemAt 0)
                        $ M.assocs variablesMap

        makeRegister i var = RegDesc i Occupied (S.singleton var)

        getRegisterNumber (Reg r) = r
        getRegisterNumber _ = willNeverHappen


        invertMap :: Map Variable (Set VariableLocation) -> Map VariableLocation (Set Variable)
        invertMap m =
            let x = M.map S.toList m
                revs = [(vl, [v]) | (v, vll) <- M.toList x, vl <- vll]
            in
                M.map S.fromList $ M.fromListWith (++) revs



setupNextBlock :: HasCallStack => Label -> Label -> MachineCodeGeneratorM ()
setupNextBlock prevNodeLabel nextNodeLabel = do
    debugTrace 10 ("setupNextBlock " ++ prevNodeLabel ++ " -> " ++ nextNodeLabel)

    nextNode <- gets ((?! nextNodeLabel) . flowGraph)
    prevNode <- gets ((?! prevNodeLabel) . flowGraph)

    -- Jeżeli prevNodeLabel == currentNode to znaczy, że instnieje
    -- szansa na potrzebę unifikacji zmiennych.

    -- Jeżeli prevNodeLabel /= currentNode to znaczy, że już obliczyliśmy
    -- wcześniej wartości końcowe tego bloku i możemy je od razu
    -- wykorzytsać.

    currentNodeLabel <- gets currentNode
    let beenHereDoneThat = prevNodeLabel /= currentNodeLabel

    unless beenHereDoneThat $ do
        -- Jesteśmy na końcu po raz pierwszy
        currentNode <- gets ((?! currentNodeLabel) . flowGraph)
        currentVars <- gets variableDescr
        let varsAliveAtEnd = M.fromSet (const 0) $ aliveEnd currentNode
            locationsOfAliveAtEnd = M.intersection currentVars varsAliveAtEnd
            varsBestLoc = M.map bestLocation locationsOfAliveAtEnd
        -- TODO przy optymalizacjach, sprawdzić czy zmienne z pamięci
        -- nie są zawsze ładowane do rejestrów w następnikach

        -- Czy mamy już narzucone jakieś wymagania?
        requiredVars <- gets (M.lookup currentNodeLabel . nodeEndDescriptons)
        (endRegs, endDesc) <- if isNothing requiredVars then do
            -- Brak wymagań, to my je możemy narzucić
            let endDesc = M.map S.singleton varsBestLoc
            let endRegs = calcRegistersState endDesc

            return (endRegs, endDesc)
        else do
            let Just rVars = requiredVars
            -- Unifikacja jest dokonywana pod koniec każdego bloku
            -- Możemy przekazać parametry wymagane
            return rVars

        -- Zapamiętujemy nasze wyjście
        modify (\s->s{nodeEndDescriptons = M.insert currentNodeLabel (endRegs, endDesc)
                                                   (nodeEndDescriptons s)})


        -- Propagujemy nasz stan końcowy do następników
        let successors = exits prevNode
        forM_ successors (\label -> do
            debugTrace 5 ("Propagacja stanu końcowego " ++ currentNodeLabel ++ " do " ++ label)
            succNodeInit <- gets (M.lookup label . initialNodeState)
            if isJust succNodeInit then do
                -- Następnik posiada stan końcowy. Jest już on poprawny.
                return ()
            else do
                _v <- gets variableDescr
                _r <- gets registerUsage
                debugTrace 4 ("Stan końcowy " ++ currentNodeLabel ++ ":\n" ++ displayState _r _v)
                -- Stan początkowy filtrujemy przez funkcje phi
                succCode <- gets (map fst . instructions . (?! label) . flowGraph)
                let phiMappings = getPhiInfo succCode []
                    incomingMappings =
                        map (second (snd . head . filter (( == prevNodeLabel) .fst)))
                        phiMappings

                -- Tłumaczymy przychodzące wartości przez mapowania

                -- WARNING below v
                -- NOTE zakładamy mapowanie zmiennych na zmienne
                let transMap = M.fromList $ map (\(Variable l, Variable r) -> (r,l)) incomingMappings
                    inputVars = M.mapKeysWith willNeverHappen (\v ->
                                M.findWithDefault v v transMap) endDesc
                    inputRegs = M.union (calcRegistersState inputVars)
                                         allRegistersFree


                debugTrace 4 ("Mapowanie stanu wyjściowego bloku " ++ prevNodeLabel
                              ++ " na stan początkowy bloku" ++ label ++ ":")
                debugTrace 4 (unlines $ map (\(loc, out) ->
                    show loc ++ " -> " ++ show out) incomingMappings)
                debugTrace 3 ("Stan początkowy " ++ label ++ ":")
                debugTrace 3 (displayState inputRegs inputVars)

                -- Ustawiamy nowy stan początkowy
                let addNewInit = M.insert label (inputRegs, inputVars)
                modify
                    (\s ->s{initialNodeState = addNewInit (initialNodeState s)})

                succNode <- gets ((?! label) . flowGraph)
                let predecessors = entries succNode
                -- oraz ustawiwamy stan końcowy każdego poprzednika
                unless (M.null inputVars) $
                    forM_ predecessors (\label -> do
                    predNodeEnd <- gets (M.lookup label . nodeEndDescriptons)
                    let outgoingMappings = map (second (snd . head . filter (( == label) .fst)))
                                                phiMappings
                        -- NOTE odwrócona kolejność względem incomingMappings      vvv
                        transMap = M.fromList $ map (\(Variable l, Variable r) -> (l,r)) outgoingMappings
                        outputVars = M.mapKeysWith willNeverHappen (\v ->
                                    M.findWithDefault v v transMap) inputVars
                        outputRegs = M.union (calcRegistersState outputVars)
                                              allRegistersFree

                    -- Jeżeli poprzednik nie ma nic ustawionego to ustawiamy
                    when (isNothing predNodeEnd) $ do

                        debugTrace 4 ("Mapowanie stanu początkowego na stan wyjściowy bloku " ++ label ++ ":\n")
                        debugTrace 4 (unlines $ map (\(loc, out) ->
                            show loc ++ " -> " ++ show out) outgoingMappings)
                        debugTrace 3 ("Stan wyjściowy " ++ label ++ ":\n")
                        debugTrace 3 (displayState outputRegs outputVars)


                        modify (\s -> s{nodeEndDescriptons =
                            M.insert label (outputRegs, outputVars) (nodeEndDescriptons s)})

                    -- Jeżeli ma coś ustawione to musi to być to samo
                    )
            )

    -- Wczytujemy stan początkowy nowego bloku
    (initRegs, initVars) <- gets ((?! nextNodeLabel) . initialNodeState)
    maxOffset <- gets maximalOffset

    let memInUse = (S.fromList . M.elems) $ M.mapMaybe getMemoryLocation initVars
    let freeMem = S.difference (S.fromList [1 .. maxOffset]) memInUse

    debugTrace 5 ("Nowy Stan:" ++ displayState initRegs initVars)
    debugTrace 5 ("Początkowa wolna pamięć:\n" ++ show (S.toList freeMem))

    debugTrace 5 ("Offset max := " ++ show maxOffset)
    -- Ładujem stan początkowy
    modify (\s -> s{registerUsage = initRegs,
                    variableDescr = initVars,
                    unusedMemory = freeMem,
                    generatedCode = M.insert nextNodeLabel [] (generatedCode s),
                    currentCode = instructions nextNode,
                    aliveBeforeCurrentInst = aliveEntry nextNode,
                    currentNode = nextNodeLabel})

    where
        displayState initRegs initVars =
            ("\nRejestry:\n"
            ++ (unlines . map show .  M.elems) initRegs)
            ++ ("\nZmienne:\n"
            ++ (unlines . map (\(v,l)
                -> show v ++ " in " ++ (show . S.toList) l) . M.assocs) initVars)

        getPhiInfo [] funcs = funcs
        getPhiInfo ((PhiFunction op mapping):rest) acc =
            getPhiInfo rest ((op, mapping):acc)
        getPhiInfo r@(_:rest) acc = acc

        calcRegistersState variablesMap =
            M.fromList  $ map ((\(i,v) -> (i, makeRegister i v))
                        . swap . second getRegisterNumber)
                        $ filter (isRegister . snd)
                        $ map (second $ setElemAt 0)
                        $ M.assocs variablesMap

        getMemoryLocation set = case setElemAt 0 set of
                                    (Mem i) -> Just i
                                    _       -> Nothing

        bestLocation = setElemAt 0

        makeRegister i var = RegDesc i Occupied (S.singleton var)

        getRegisterNumber (Reg r) = r
        getRegisterNumber _ = willNeverHappen

        isRegister (Reg _) = True
        isRegister _ = False



noUsageAnymore :: Integer
noUsageAnymore = -1

isUsedInFuture :: Variable  -> MachineCodeGeneratorM Bool
isUsedInFuture var = do
    cCode <- gets currentCode
    cNodeLabel <- gets (currentNode)
    aliveAtEnd <- gets (aliveEnd . (?! cNodeLabel) . flowGraph)

    return $ S.member var aliveAtEnd || S.member var (snd (head cCode))

getVariableNextUse :: Variable -> AliveAtCode -> Integer
getVariableNextUse var code = _getVariableNextUse var code 0
    where
        _getVariableNextUse var [] i = i
        _getVariableNextUse var ((code, alive):rest) i
            | S.notMember var alive = noUsageAnymore
            | isUsed (Variable var) code = i
            -- żywa ale jeszcze nie użyta
            | otherwise = _getVariableNextUse var rest (i+1)


        isUsed var (ValueCode _ oper) = checkOper var oper
        isUsed var (ReferenceCode _ oper) = checkOper var oper
        isUsed var (FlowCtrlCode fctrl) = case fctrl of
            (ConditionalFull a _ b _ _) -> a == var || b == var
            (Return a) -> a == var
            _ -> False
        isUsed _ _ = False

        checkOper var oper = case oper of
            (Binary a binop b)  -> a == var || b == var
            (Unary unrop a)     -> a == var
            (LoadAddressFull a b o s)   -> a == var || b == var
            (LoadAddressArray a b o)    -> a == var || b == var
            (LoadAddressOffset a o)     -> a == var
            (LoadFrom a)    -> a == var
            (CopyOf a)      -> a == var
            (Call callLabel operands) -> var `elem` operands
            (CallReg a operands) -> a == var || var `elem` operands


-- works for infinite lists
firstElemSatisfying :: Foldable t => (a -> Bool) -> t a -> Maybe a
firstElemSatisfying p = foldr (\x a -> if p x then Just x
                                       else if isJust a then a
                                       else Nothing) Nothing

allocateMoreStack :: MachineCodeGeneratorM Offset
allocateMoreStack = do
    offset <- gets maximalOffset
    modify (\s -> s{maximalOffset = offset + 1})
    debugTrace 0 ("allocateMoreStack stack:" ++ show (offset + 1))
    return (offset + 1)

allocateLocationOtherThan :: [Register] -> MachineCodeGeneratorM VariableLocation
allocateLocationOtherThan constraints = do
    debugTrace 0 "allocateLocation"
    maybeReg <- tryFreeRegisterOtherThan constraints
    if isNothing maybeReg then do
        -- Przypisujemy zmienną do pamięci
        freeMem <- gets unusedMemory
        mem <- if S.null freeMem then do
            allocateMoreStack
        else do
            let addr = setElemAt 0 freeMem
            modify (\s -> s{unusedMemory = S.delete addr freeMem})
            return addr

        return (Mem mem)
    else do
        let Just regnum = maybeReg
        return (Reg regnum)

allocateLocation :: MachineCodeGeneratorM VariableLocation
allocateLocation = allocateLocationOtherThan []



allocateNewVariable :: HasCallStack => Variable -> MachineCodeGeneratorM VariableLocation
allocateNewVariable var = do
    newLoc <- allocateLocation
    addVariableLocation var newLoc
    case newLoc of
        (Reg r) -> do
            allocRegister var r     -- NOTE czy to jest okej?
                                    -- teoretycznie rejestr jest 'wolny'
        _ -> do return ()

    return newLoc



-- Wykonuje zapis rejestru do wolnej pamięci
-- WARNING nie akutalizuje opisów!
saveToMemory :: Register -> MachineCodeGeneratorM VariableLocation
saveToMemory regnum = do
    freeMem <- gets unusedMemory
    mem <- if S.null freeMem then do
        newMem <- allocateMoreStack
        emit $ instr2 "mov" (Mem newMem) (Reg regnum)
        return newMem
    else do
        let offset = (setElemAt 0 freeMem)
        emit $ instr2 "mov" (Mem offset) (Reg regnum)
        return offset

    -- aktualizacja zajętości
    modify (\s -> s{unusedMemory = S.delete mem freeMem})

    return (Mem mem)


saveRegisterToMemory :: Register -> MachineCodeGeneratorM VariableLocation
saveRegisterToMemory reg = do
    regDesc <- gets ((?! reg) . registerUsage)
    save <- saveToMemory reg
    forM_ (contents regDesc) (`addVariableLocation` save)
    _freeRegister reg
    return save

-- TODO to jest wysoce nieoptymalne
spillNonFree :: RegisterDescription -> MachineCodeGeneratorM ()
spillNonFree rd = do
    debugTrace 0 ("spillNonFree " ++ show (Reg $ number rd))
    unless (isFreeRegister rd) $ do
                            save <- saveToMemory (number rd)
                            forM_ (contents rd) (`addVariableLocation` save)
                            _freeRegister (number rd)

    where isFreeRegister rd = regstate rd == Free

spillSomethingOtherThan :: [Register] -> MachineCodeGeneratorM Register
spillSomethingOtherThan constraints = do
    let constrS = S.fromList (map Reg constraints)
    -- Wiemy, że nie ma wolnego rejestru spośród poszukiwanych
    -- Wybieramy zmienną, która:
    --  1. posiada więcej niż jeden rejestr
    --  2. jest zapisana gdzieś w pamięci i posiada rejestr
    --  3. jest zapisana tylko w pojedynczym rejestrze
    varUse <- gets variableDescr
    -- FIXME Sprawdzić czy rejestr nie przechowuje żadnej brudnej zmiennej
    let locationSplits = M.map (S.spanAntitone isRegister) varUse
        correctRegs = M.map (first (`S.difference` constrS)) locationSplits
        maybeTwoRegs = firstElemSatisfying twoRegisterVar correctRegs
        maybeRegMem  = firstElemSatisfying regAndMemVar correctRegs
        maybeOnlyReg = firstElemSatisfying onlyRegister correctRegs

    if isJust maybeTwoRegs then do
        let Just (rset, _) = maybeTwoRegs
        reg <- freeFirstRegister rset
        debugTrace 0 ("spilling (Two registers)" ++ blueColor (show reg))
        return reg
    else if isJust maybeRegMem then do
        let Just (rset, _) = maybeRegMem
        reg <- freeFirstRegister rset
        debugTrace 0 ("spilling (register & memory)" ++ blueColor (show reg))
        return reg
    else do
        regUse <- gets registerUsage
        let Just (rset, _) = maybeOnlyReg
            (Reg regnum) = setElemAt 0 rset
            regDesc = regUse ?! regnum

        savedAt <- saveToMemory regnum
        -- Zakutalizować pozycję wszystkich zmiennych
        forM_ (contents regDesc) (`addVariableLocation` savedAt)
        -- Zwolnić rejestr
        _freeRegister regnum
        debugTrace 0 ("spilling (Only register) " ++ blueColor (show (Reg regnum)))
        return regnum

    where
        twoRegisterVar (rset, _) = S.size (S.filter isRegister rset) >= 2
        regAndMemVar (rset, mset) = not (S.null rset) && not (S.null mset)
        onlyRegister (rset, mset) = S.null mset && not (S.null rset)
        freeFirstRegister set = do
            let (Reg regnum) = setElemAt 0 set
            _freeRegister regnum
            return regnum

        isRegister (Reg _) = True
        isRegister _ = False

        meetsCriteria rd = notElem (number rd) constraints



spillSomething :: MachineCodeGeneratorM Register
spillSomething =  spillSomethingOtherThan []

preserveRegister :: Register -> [Register] -> Bool -> MachineCodeGeneratorM ()
preserveRegister r constraints backward = do
    debugTrace 0 ("Preservation of " ++ x86_64registers!!r ++ " not to " ++ show constraints)
    regUse <- gets registerUsage
    varUse <- gets variableDescr
    cCode <- gets currentCode
    (code,aliveAfter) <- gets (head . currentCode)
    aliveNow <- if backward then gets aliveBeforeCurrentInst else return S.empty
    debugTrace 0 ("Variables alive after: " ++ show (S.toList aliveAfter))
    debugTrace 0 ("Variables alive before: " ++ show (S.toList aliveNow))
    let rd = regUse ?! r
        worth = S.union aliveNow aliveAfter
        sConst = S.fromList (map Reg constraints)
    debugTrace 0 (x86_64registers!!r ++ " -- " ++ show rd)

    if S.null (contents rd ) then return ()
    else do
        let variablesHere = M.restrictKeys varUse (contents rd)

            variablesOnlyInConstrained =
                M.keysSet $ M.filter (S.null . (`S.difference` sConst)) variablesHere

            variablesOnlyHere = M.keysSet $ M.filter (( == 1) . S.size) variablesHere

            variablesToPreserve = S.union variablesOnlyHere variablesOnlyInConstrained

            liveVariableOnlyHere = S.filter (`S.member` worth) variablesToPreserve


        debugTrace 0 ("Worth variables in " ++ x86_64registers!!r ++ " "++ show  liveVariableOnlyHere)
        unless (null liveVariableOnlyHere) $ do
            debugTrace 0 (show liveVariableOnlyHere ++ " in " ++ x86_64registers!!r ++ "require preservation")
        -- Są zmienne, które żyją i są tylko w tym rejestrze
            newLoc <- allocateLocationOtherThan constraints
            emit $ InstructionComment (instr2 "mov" newLoc (Reg $ number rd))
                                    "preservation"
            case newLoc of
                (Reg r) ->  forM_ (contents rd) (\var -> do
                                    addVariableLocation var newLoc
                                    allocRegister var r
                            )
                (Mem m) ->  forM_ (contents rd) (\var -> do
                                addVariableLocation var newLoc
                            )
                _ -> willNeverHappen
        let notWorth = S.toList $ S.difference (contents rd) (liveVariableOnlyHere)
        debugTrace 0 (show notWorth ++ " in " ++ x86_64registers!!r ++ " do not require preservation")
        varUse <- gets variableDescr
        debugTrace 0 (__prettyPrintVariables varUse)

preserveVariablesLocation :: VariableLocation -> MachineCodeGeneratorM ()
preserveVariablesLocation (Imm i) = return ()
preserveVariablesLocation (Mem i) = return ()
preserveVariablesLocation (Reg r) = preserveRegister r [] False



addRegisterAsUsed :: RegisterDescription -> MachineCodeGeneratorM ()
addRegisterAsUsed reg = modify (\s -> s{usedRegisters = S.insert (number reg)
                                                        (usedRegisters s)})

getFreeDistinctRegistersOtherThan :: Int -> [Register] -> MachineCodeGeneratorM [Register]

getFreeDistinctRegistersOtherThan reqRegs constraints = do
    debugTrace 50 ("get (" ++ show reqRegs ++ ") FreeDistincRegistersOtherThan " ++ show constraints)

    when (reqRegs > length x86_64registers - length constraints) waltIDontKnowMan
    regDescs <- gets registerUsage
    let goodRegisters = M.filter meetsCriteria regDescs
    let takenRegs = M.take reqRegs goodRegisters -- Can be not enought of them

    if M.size goodRegisters >= reqRegs then do
        forM_ takenRegs addRegisterAsUsed
        return (M.keys takenRegs)
    else do -- Not enough of them, we need to spill others
        -- We take what we have and tag it as new constraints
        let newConstraints = S.union (S.fromList constraints) (M.keysSet takenRegs)
            regsLeft = reqRegs - M.size goodRegisters

        finalConstrs <- foldM (\cs _ -> do
            -- Spill something other than constrained
            spilled <- spillSomethingOtherThan (S.toList cs)
            -- Add spilled to new constraints
            return (S.insert spilled cs)
            ) newConstraints (replicate regsLeft ())

        let usedRegs = S.difference finalConstrs (S.fromList constraints)
        debugTrace 50 ("Used registers: " ++ show (map (x86_64registers!!) (S.toList usedRegs)))
        forM_ usedRegs (addRegisterAsUsed . (regDescs ?!))
        return (S.toList usedRegs)
    where
        meetsCriteria rd =  notElem (number rd) constraints
                         && (regstate rd == Free)




tryFreeRegisterOtherThan :: [Register] -> MachineCodeGeneratorM (Maybe Register)
tryFreeRegisterOtherThan [] = tryFreeRegister
tryFreeRegisterOtherThan constraints = do
    debugTrace 5 ("tryFreeRegisterOtherThan " ++ show constraints)
    reg <- gets (firstElemSatisfying isFreeRegisterC . registerUsage)
    if isNothing reg then do
        debugTrace 5 ("\t there is no free register.")
        return Nothing
    else do
        let Just register = reg
        addRegisterAsUsed register
        debugTrace 5 ("\t there is " ++ x86_64registers !! (number register) ++ " free.")
        return $ Just (number register)
    where
        isFreeRegisterC rd = notElem (number rd) constraints
                             && (regstate rd == Free)

getFreeRegister :: MachineCodeGeneratorM Register
getFreeRegister = do
    reg <- gets (firstElemSatisfying isFreeRegister . registerUsage)
    if isNothing reg then do
        spilled <- spillSomething
        debug ("Spilling! Freed " ++ show spilled)
        return spilled
    else do
        let Just register = reg
        addRegisterAsUsed register
        return $ number register
    where isFreeRegister rd = regstate rd == Free

tryFreeRegister :: MachineCodeGeneratorM (Maybe Register)
tryFreeRegister = do
    reg <- gets (firstElemSatisfying isFreeRegister . registerUsage)
    if isNothing reg then
        return Nothing
    else do
        let Just register = reg
        addRegisterAsUsed register
        return $ Just (number register)
    where isFreeRegister rd = regstate rd == Free

markRegister :: Register -> RegisterState -> MachineCodeGeneratorM ()
markRegister reg rstate = do
    regUse <- gets registerUsage
    let regDesc = regUse ?! reg
    modify (\s -> s{registerUsage = M.insert reg regDesc{regstate = rstate} (registerUsage s)})

allocRegister :: Variable -> Register -> MachineCodeGeneratorM ()
allocRegister var num = do
    regDesc <- gets ((?! num) . registerUsage)
    varDesc <- gets ((?! var) . variableDescr)
    regUse <- gets registerUsage
    varUse <- gets variableDescr
    let newRegData = regDesc{regstate = Occupied, contents = S.insert var (contents regDesc)}
        newVarData = S.insert (Reg num) varDesc

    modify (\s -> s{registerUsage = M.insert num newRegData (registerUsage s),
                    variableDescr = M.insert var newVarData (variableDescr s)})

_freeRegister :: Register -> MachineCodeGeneratorM ()
_freeRegister num = do
    varUse <- gets variableDescr
    regUse <- gets registerUsage
    let regDesc = regUse ?! num

    -- Usunąć rejestr jako lokację dotychczasowych zmiennych
    let noRegVarUsage = M.map (invalidateReg num) varUse
        newRegUsage = M.insert num regDesc{regstate = Free,
                                           contents = S.empty} regUse

    modify (\s -> s{variableDescr = noRegVarUsage, registerUsage = newRegUsage})

    where
        invalidateReg regnum = S.delete (Reg regnum)

-- Rejestr otrzymał nową unikalną wartość
updateRegister :: Register -> Variable -> MachineCodeGeneratorM ()
updateRegister num var = do
    _freeRegister num

    regDesc <- gets ((?! num) . registerUsage)
    varUse <- gets variableDescr

    -- Dopisać rejestr jako lokację nowej zmiennej
    let newVarLocations = S.insert (Reg num) (M.findWithDefault S.empty var varUse)
        newVarUsage = M.insert var newVarLocations varUse

    -- Zaktualizować zawartość rejestru
    newRegUsage <- gets (M.insert num
                         regDesc{regstate = Occupied,
                                  contents = S.singleton var} . registerUsage)

    modify (\s -> s{variableDescr = newVarUsage,
                    registerUsage = newRegUsage})
    where
        invalidateReg regnum = S.delete (Reg regnum)

-- zmienna przestaje być żywa
freeVariable :: Variable -> MachineCodeGeneratorM ()
freeVariable var = do
    debugTrace 0 ("freeVariable " ++ show var )
    regUse <- gets registerUsage
    varUse <- gets variableDescr

    -- Unieważnić rejestry przechowujące var
    let newRegUsage = M.map (invalidateVar var) regUse
        newVarUsage = M.delete var varUse

    modify (\s -> s{registerUsage = newRegUsage,
                    variableDescr = newVarUsage})

    where
        invalidateVar var regDesc =
            let newContents = S.delete var (contents regDesc) in
                if S.null newContents then
                    regDesc{contents = newContents, regstate = Free}
                else
                    regDesc{contents = newContents}

removeVariableLocation :: Variable -> VariableLocation -> MachineCodeGeneratorM ()
removeVariableLocation var vl = do
    varUse <- gets variableDescr
    let varDesc = S.delete vl (varUse ?! var)

    modify (\s -> s{variableDescr = M.insert var varDesc varUse})

addVariableLocation :: Variable -> VariableLocation -> MachineCodeGeneratorM ()
addVariableLocation var vl = do
    debugTrace 0 ("addVariableLocation " ++ show var ++ " -> " ++ show vl)
    varUse <- gets variableDescr
    let varDesc = S.insert vl (M.findWithDefault S.empty var varUse)

    modify (\s -> s{variableDescr = M.insert var varDesc varUse})

    when (isRegister vl) $
        allocRegister var (extractRegister vl)


safeAllVariableLocations :: Variable -> MachineCodeGeneratorM (Set VariableLocation)
safeAllVariableLocations var = gets (M.findWithDefault S.empty var . variableDescr)

getAllVariableLocations :: Variable -> MachineCodeGeneratorM (Set VariableLocation)
getAllVariableLocations var = do
    gets (M.findWithDefault variableError var . variableDescr)
    where
        variableError = error ("Variable " ++ show var ++ " has no locations")

removeDeadVariables :: HasCallStack => MachineCodeGeneratorM ()
removeDeadVariables = do
    debugTrace 0 ("removeDeadVariables")
    varUsage <- gets variableDescr
    (_, alive):rest <- gets currentCode
    forM_ (M.keys varUsage) (\var -> do
        unless (S.member var alive) $ do
            debugTrace 0 ("Removing " ++ show var)
            freeVariable var
        )

-- a := b
updateVariable :: HasCallStack => Variable -> Variable -> MachineCodeGeneratorM ()
updateVariable a b = do
    -- NOTE to nie będzie w ogóle wymagane przy lepszym SSAT!!!!
    aLoc <- allocateNewVariable a
    bLoc <- getBestVariableLocation b
    emit $ InstructionComment (instr2 "mov" aLoc bLoc) (show a ++ " := " ++ show b)
    {-
    debugTrace 0 ("updateVariable " ++ show a ++ " " ++ show b)
    regUse <- gets registerUsage
    varUse <- gets variableDescr

    -- Unieważnić rejestry przechowujące a
    let newRegUsage = M.map (invalidateVar a) regUse

    -- wszystkie lokacje b to teraz lokacje a
    let bLocations = varUse ?! b
        newVarUsage = M.insert a bLocations varUse

    -- NOTE co w przypadku rejestrów?
    -- Czy należy dodać zmienną a do contentu rejestrów?

    let addedToRegs = M.map (\rd ->
            if S.member b (contents rd) then
                rd{contents = S.insert a (contents rd)}
            else rd
            ) newRegUsage


    modify (\s -> s{registerUsage = addedToRegs,
                    variableDescr = newVarUsage})

    mapM_ (\case
                (Reg r) -> do
                    allocRegister a r
                _   -> return ()
            ) (S.toList bLocations)

    debug ("\tnew " ++ show a ++ " locations: " ++ show bLocations)
    where
        invalidateVar var regDesc =
            let newContents = S.delete var (contents regDesc) in
                if S.null newContents then
                    regDesc{contents = newContents, regstate = Free}
                else
                    regDesc{contents = newContents}
-}


loadAllWithConstraints :: [Operand] -> [Register] -> Bool
                       -> MachineCodeGeneratorM [(Operand,VariableLocation)]
loadAllWithConstraints operands constraints forceRegister = do
    debugTrace 50 ("loadAllWithConstraints " ++ show constraints ++ " force: " ++ show forceRegister)
    let constrS = S.fromList (map Reg constraints)
    regDesc <- gets registerUsage
    varUse <- gets variableDescr

    let (variablesOnlyOps, immediates) = L.partition isVariable operands
        variablesOnly = S.fromList $ map (\(Variable v) -> v) variablesOnlyOps
        (goodToGo, toLoad) = M.partition (inGoodRegisters constrS) (M.restrictKeys varUse variablesOnly)
        goodVarRegs = M.map (getOneGoodReg constrS) goodToGo

        sizeToLoad =    if forceRegister then
                            M.size toLoad + length immediates
                        else
                            M.size toLoad

    regs <- getFreeDistinctRegistersOtherThan sizeToLoad (M.elems goodVarRegs)

    let pairVarToReg = zip (M.keys toLoad) regs

    forM_ pairVarToReg (\(var, reg) -> do
        varLoc <- getBestVariableLocation var
        emit $ instr2 "mov" (Reg reg) varLoc
        addVariableLocation var (Reg reg)
        allocRegister var reg
        )

    let goodVarsRetList = map (bimap Variable Reg) $ M.assocs goodVarRegs
        loadedVarsRetList = map (bimap Variable Reg) pairVarToReg

    immRetList <- if forceRegister then do
                    let leftRegs = drop (M.size toLoad) regs
                        immRegPair = zip immediates leftRegs
                    mapM (\(Immediate i, reg) -> do
                            emit $ instr2 "mov" (Reg reg) (Imm i)
                            return (Immediate i, Reg reg)
                        ) immRegPair
                    else 
                        return $ map (\(Immediate i) -> (Immediate i, Imm i)) immediates
        
    return (immRetList ++ goodVarsRetList ++ loadedVarsRetList)

    where
        inGoodRegisters constrS varLocations =
            (not . S.null) $ S.intersection constrS varLocations

        getOneGoodReg constrS varLocations =
            extractRegister $ setElemAt 0 (S.intersection constrS varLocations)
        

loadAvoiding :: Operand -> [VariableLocation] -> Bool -> MachineCodeGeneratorM VariableLocation
loadAvoiding op vls forceRegister = do
    let x = map extractRegister $ filter isRegister vls
    snd . head <$> loadAllWithConstraints [op] x forceRegister


-- TODO dopisać zapamiętywanie tego załadowania
loadIfNotRegister :: Variable -> VariableLocation -> MachineCodeGeneratorM VariableLocation
loadIfNotRegister var vl@(Mem off) = do
    reg <- getFreeRegister
    emit $ instr2 "mov" (Reg reg) vl
    addVariableLocation var (Reg reg)
    allocRegister var reg
    return (Reg reg)

loadIfNotRegister _ (Reg reg) = return (Reg reg)

loadIfNotRegister _ (Imm i) = do
    reg <- getFreeRegister
    emit $ instr2 "mov" (Reg reg) (Imm i)
    return (Reg reg)

loadIfNotRegisterOp :: Operand -> VariableLocation -> MachineCodeGeneratorM VariableLocation
loadIfNotRegisterOp (Immediate i) vl = do
    reg <- getFreeRegister
    emit $ instr2 "mov" (Reg reg) (Imm i)
    return (Reg reg)

loadIfNotRegisterOp (Variable v) vl = loadIfNotRegister v vl
-- Jeżeli wartość jest żywa po aktualnej operacji, spróbuj przypisać ją
-- do wolnego rejestru
sustainIfUsedAgain :: Operand -> VariableLocation -> MachineCodeGeneratorM VariableLocation
sustainIfUsedAgain (Immediate i) vl = return vl
sustainIfUsedAgain (Variable var) vl = do
    debugTrace 0 ("sustainIfUsedAgain " ++ show var)
    instr <- gets (head . currentCode)
    let isAlive = S.member var (snd instr)
    varRegs <- gets (S.size . S.filter isRegister . (?! var) . variableDescr)

    if isAlive && varRegs < 2 then do
        usage <- isUsedInFuture var
        if usage then do
            debugTrace 0 ("Zmienna " ++ show var ++ " nie zostanie już użyta w tym bloku")
            return vl
        else do
            reg <- tryFreeRegister
            if isNothing reg then
                return vl
            else do

                let Just num = reg
                varLoc <- getBestVariableLocation var

                emit $ InstructionComment (instr2 "mov" (Reg num) varLoc) "sustaining"

                addVariableLocation var (Reg num)

                allocRegister var num

                return (Reg num)
    else do
        debugTrace 0 ("Variable " ++ show var ++ redColor " is dead")
        return vl
    where isRegister (Reg r) = True
          isRegister _ = False


sustainIfUsedAgain _ _ = willNeverHappen


getBestVariableLocation :: HasCallStack => Variable -> MachineCodeGeneratorM VariableLocation
getBestVariableLocation var = do
    debugTrace 10 ("getBestVariableLocation " ++ show var)
    varLocations <- gets ((?! var) . variableDescr)
    -- Dzięki właściwości Ord dla VariableLocation priorytetyzuje rejestry
    return $ setElemAt 0 varLocations
    where
        inRegister (Reg _) = True
        inRegister (Mem _) = False

getOperandLocation :: HasCallStack => Operand -> MachineCodeGeneratorM VariableLocation
getOperandLocation (Variable var) = getBestVariableLocation var
getOperandLocation (Immediate i) = return (Imm i)
getOperandLocation _ = willNeverHappen


isOperandIn (Variable var) rd = S.member var (contents rd)
isOperandIn _ _ = False

{-------------------------------------------------------------------------------
            Obsługa poszczególnych instrukcji kodu czwórkowego
-------------------------------------------------------------------------------}



-- TODO ulepszyć w przypadku stałych
handleValBinOP :: HasCallStack => Bool -> Variable -> ValueOper -> MachineCodeGeneratorM ()
handleValBinOP memaccess varA (Binary b binop c) = 
    case binop of
    Add -> classicHandler memaccess varA b c "add"
    Sub -> classicHandler memaccess varA b c "sub"
    Mul -> classicHandler memaccess varA b c "imul"
    Div -> divisionHandler memaccess varA b c True
    Mod -> divisionHandler memaccess varA b c False
    where
        -- Wybrać rejestr do przeprowadzenia operacji:
        --  najlepiej rejestr R, w który już jest B
        --      jeżeli B żyje dalej, to można spróbować skopiować jej wartość
        --      do innego rejestru R'
        -- Wziąć dowolną lokację C i wykonać:  R := R op C
        -- Następnie chcemy zapisać, że od teraz A jest w R i R przechowuje A
        -- Jeżeli B i C były stałymi, nic się nie zmienia
        classicHandler memaccess varA b c str = do
            bLoc <- getOperandLocation b >>= loadIfNotRegisterOp b >>= sustainIfUsedAgain b
            cLoc <- getOperandLocation c >>= sustainIfUsedAgain c

            -- Nie chcemy przez przypadek wykorzystać jedynej lokacji b
            preserveVariablesLocation bLoc
            emit $ instr2 str bLoc cLoc

            
            if memaccess then do
                aLoc <- getBestVariableLocation varA >>= loadIfNotRegister varA
                emit $ Instruction2 "mov" (asAddress aLoc) (asMachine bLoc)
            else do
                let (Reg num) = bLoc
                updateRegister num varA

        -- Dzielenie wymaga użycia specjalnych rejestrów EAX:EDX
        divisionHandler memaccess varA b c isDiv = do
            regUse <- gets registerUsage

            let
                raxDesc = regUse ?! rax
                rdxDesc = regUse ?! rdx
                rsDesc = regUse ?! (registerNumber "r11")

            -- Sprawdzanie lokalizacji C
            -- C nie może być: w RAX, w RDX
            cDivLoc <- prepareLocation [rax, rdx] rsDesc >>= sustainIfUsedAgain c

            -- zwalniamy RDX
            -- liftIO $ traceIO ("freeing " ++ show rdx)
            spillNonFree rdxDesc

            if isOperandIn b raxDesc then
                -- Jeżeli b jest już w RAX, to nie chcemy jej nadpisać
                preserveVariablesLocation (Reg rax)
            else do
                -- zwalniamy RAX
                -- liftIO $ traceIO (show b ++ " is not in " ++ show rax)
                spillNonFree raxDesc
                bLoc <- getOperandLocation b
                emit $ instr2 "mov" (Reg rax) bLoc

            -- c w pamięci lub R8
            -- b w RAX
            emit $ Instruction0 "cqo"
            emit $ instr1 "idiv" cDivLoc
            -- wynik dzielenia w RAX
            -- wynik modulo w RDX
            if memaccess then do
                aLoc <- snd . head <$> loadAllWithConstraints [Variable varA] [rax, rdx] True
                if isDiv then do
                    emit $ Instruction2 "mov" (asAddress aLoc) (asMachine (Reg rax))
                else do
                    emit $ Instruction2 "mov" (asAddress aLoc) (asMachine (Reg rdx))
            else do
                if isDiv then do
                    updateRegister rax varA
                else do
                    updateRegister rdx varA
            -- Pozostałe rejestry pozostają wolne
            -- (nie zmieniliśmy ich stanu po zwolnieniu przed dzieleniem)

        isImmediate (Imm _) = True
        isImmediate _ = False

        prepareLocation invalidRegs rs = do
            case c of
                (Variable var) -> do
                    cLocations <- getAllVariableLocations var
                    -- debug ("Preping loc for " ++ show var ++ " with locs: " ++ show cLocations)
                    let okLocation = firstElemSatisfying (isProperLocation invalidRegs)
                                                        cLocations
                    if isNothing okLocation then do
                        -- TODO to można polepszyć dokonując spill z ograniczeniami
                        maybeFreeReg <- tryFreeRegisterOtherThan invalidRegs
                        useThisOrSpecial maybeFreeReg rs (setElemAt 0 cLocations)

                    else let Just okLoc = okLocation in
                        return okLoc
                (Immediate i) -> do
                    maybeFreeReg <- tryFreeRegisterOtherThan invalidRegs
                    useThisOrSpecial maybeFreeReg rs (Imm i)


            where useThisOrSpecial maybeFreeReg rs loc  =
                    if isNothing maybeFreeReg then do
                            spillNonFree rs

                            emit $ instr2 "mov" (Reg (number rs)) loc
                            return (Reg $ number rs)
                        else do
                            let Just freeReg = maybeFreeReg
                            emit $ instr2 "mov" (Reg freeReg) loc
                            return $ Reg freeReg

        isProperLocation regConstr (Reg num) = num `notElem` regConstr
        isProperLocation _ (Imm _) = True
        isProperLocation _ _ = False

handleUnrOp :: Variable -> UnrOp -> Operand -> StateT MachineCodeGeneratorState IO ()
handleUnrOp lhs Neg a = do
    aLoc <- getOperandLocation a >>= loadIfNotRegisterOp a
    preserveVariablesLocation aLoc

    emit $ instr1 "neg" aLoc

    let (Reg num) = aLoc
    updateRegister num lhs

handleUnrOp lhs Not a = do
    aLoc <- getOperandLocation a
    lhsLoc <- allocateNewVariable lhs

    case aLoc of
        (Imm i) ->
            if i == 0 then
                emit $ Instruction2 "mov" (asMachine lhsLoc) (ImmediateInt 1)
            else
                emit $ Instruction2 "mov" (asMachine lhsLoc) (ImmediateInt 0)
        _ -> do
            tmp <- Reg <$> getFreeRegister
            -- Ustawiamy lhsLoc na 1
            emit $ Instruction2 "mov" (asMachine tmp) (ImmediateInt 1)
            emit $ instr2 "xor" lhsLoc lhsLoc
            emit $ instr2 "test" aLoc (Imm (-1))
            -- Jeżeli aLoc == 0, czyli fałsz, to ustawiamy 
            emit $ instr2 "cmovz" lhsLoc tmp
            






handleCopyOf :: HasCallStack => Bool -> Variable -> Operand -> MachineCodeGeneratorM ()
handleCopyOf memaccess lhs rhs = do
    when memaccess $ debugTrace 1000 ("handleCopyOf ["++ show lhs ++"] <- " ++ show rhs)
    (instr, alive):_ <- gets currentCode

    if (not memaccess) && not (S.member lhs alive) then do
            debugTrace 1000 ("Copy instruction " ++ show lhs ++ " := " ++ show rhs ++ redColor " is pointless")
            return ()

    else
        if memaccess then do
            debugTrace 100 ("CopyOf with memory access:\n")
            lhsLoc <- getBestVariableLocation lhs >>= loadIfNotRegister lhs
            case rhs of
                (Immediate i) -> do
                    emit $ Instruction2 "mov" (asAddress lhsLoc) (ImmediateInt i)
                    
                (Variable varRHS) -> do
                    let Reg r = lhsLoc
                    
                    [(_, rhsLoc)] <- loadAllWithConstraints [rhs] [r] False
                    
                    
                    emit $ Instruction2 "mov" (asAddress lhsLoc) (asMachine rhsLoc)
                _ -> error ("handleCopyOf " ++ show lhs ++ " " ++ show rhs)
        else case rhs of
        (Immediate i) -> do
            -- Jeżeli zmienna posiada rejestr to zapisać pod rejestr
            -- i unieważnić pozostałe lokacje
            -- Jeżeli to nowa zmienna to zaalokwać dla niej miejsce na stosie
            -- i zapisać do pamięci
            -- Jeżeli zmienna nie posiada rejestru to zapisać do pamięci
            -- i unieważnić pozostałe lokacje
            locs <- safeAllVariableLocations lhs
            newLocation <- if S.null locs then do
                debugTrace 0 ("Variable " ++ show lhs ++ "has not been allocated")
                allocateNewVariable lhs
            else case setElemAt 0 locs of
                    (Reg regnum) -> do
                        freeVariable lhs
                        addVariableLocation lhs (Reg regnum)
                        return (Reg regnum)
                    (Mem x) -> do
                        freeVariable lhs
                        addVariableLocation lhs (Mem x)
                        return (Mem x)

            emit $ instr2 "mov" newLocation (Imm i)
        (Variable varRHS) -> updateVariable lhs varRHS
        _ -> error ("handleCopyOf " ++ show lhs ++ " " ++ show rhs)

handleLoadFrom :: HasCallStack => Bool -> Variable -> Operand -> MachineCodeGeneratorM ()
handleLoadFrom memaccess lhs rhs = do
    if memaccess then
        debugTrace 0 ("handleLoadFrom "++ show lhs ++" <- [" ++ show rhs ++ "]")
    else
        debugTrace 0 ("handleLoadFrom ["++ show lhs ++"] <- [" ++ show rhs ++ "]")
    
    (instr, alive):_ <- gets currentCode
    if not (S.member lhs alive) && not memaccess then do
            debugTrace 0 ("Load instruction " ++ show lhs ++ " := " ++ show rhs ++ redColor " is pointless")
            return ()
    else case rhs of
        (Immediate i) ->
            if memaccess then do
                lhsLoc <- getBestVariableLocation lhs >>= loadIfNotRegister lhs
                emit $ Instruction2 "mov" (asAddress lhsLoc) (asAddress (Imm i))
            else do
                reg <- getFreeRegister
                emit $ Instruction2 "mov" (asMachine $ Reg reg) (asAddress (Imm i))
                addVariableLocation lhs (Reg reg)

        (Variable rhsVAR) ->
            if memaccess then do
                lhsLoc <- getBestVariableLocation lhs
                rhsLoc <- getBestVariableLocation rhsVAR
                waltIDontKnowMan


            else do
                rhsLoc <- getBestVariableLocation rhsVAR >>= loadIfNotRegister rhsVAR
                lhsLoc <- allocateNewVariable lhs
                emit $ Instruction2 "mov" (asMachine lhsLoc) (asAddress rhsLoc)
                addVariableLocation lhs lhsLoc
                addVariableLocation rhsVAR rhsLoc

        _ -> willNeverHappen

handleCall :: HasCallStack => Variable -> Either Label Operand -> [Operand] -> MachineCodeGeneratorM ()
handleCall lhs address ops = do
    let argsnum = length ops
        inRegs  = min x86_64ABIMaxRegisters argsnum
        onStack = max 0 (argsnum - x86_64ABIMaxRegisters)
        abiRegsUsed = take inRegs x86_64ABIregisters
        volatileRegs = map registerNumber x86_64VolatileRegisters

    let registerArguments = zipWith (\o r -> (o, registerNumber r)) ops abiRegsUsed

    -- Załadować zmienne
    forM_ registerArguments (\(op, regnum) -> do
        regDesc <- gets ((?! regnum) . registerUsage)
        debugTrace 0 ("Freeing " ++ show (Reg regnum))

        if (not $ isOperandIn op regDesc) then do
            preserveRegister regnum volatileRegs True
            opLoc <- getOperandLocation op
            emit $ InstructionComment (instr2 "mov" (Reg regnum) opLoc) "call argument"
            -- Ten rejestr nie jest już lokalizacją starej zmiennej
            -- ani nie używamy go jako lokalizacji nowej zmiennej
            _freeRegister regnum
        else preserveRegister regnum volatileRegs False


        case op of
            (Variable var) -> do
                debugTrace 0 (show var ++ " -> " ++ show (Reg regnum))
                updateRegister regnum var
            _ -> return ()

        )

    let restRegs = S.difference (S.fromList volatileRegs) (S.fromList (map registerNumber abiRegsUsed))

    -- Zwolnić odpowiednią liczbę rejestrów ulotnych
    forM_ restRegs (\regnum -> do
        rd <- gets ((?! regnum) . registerUsage)
        debugTrace 0 ("Freeing rest " ++ show (Reg regnum))
        unless (regstate rd == Free) $
            preserveRegister regnum volatileRegs False
        )

    -- Załadować dodatkowe argumenty na stos
    when (odd onStack)
        (emit $ InstructionComment (Instruction0 "sub rsp, 8") "\t; stack alignment")

    let stackArguments = sortReverse $ zip (drop inRegs ops) [0..]
    forM_ stackArguments (\(op,num) -> do
            opLoc <- getOperandLocation op
            emit $ instr1 "push" opLoc
            )

    if isLeft address then do
        let Left label = address
        emit $ Instruction1 "call" (ToLabel label)
    else do
        let Right addrOper = address
        addrLoc <- getOperandLocation addrOper
        emit $ Instruction1 "call" (asMachine addrLoc)

    -- Ustawić rejestry jako wolne (po wywołaniu call)
    forM_ volatileRegs (\regnum -> do
        _freeRegister regnum
        )

    if (odd onStack) then
        emit $ Instruction0 ("add rsp, " ++ show (8*(onStack + 1)))
    else when (onStack /= 0)
        (emit $ Instruction0 ("add rsp, " ++ show (8*onStack)))


    addVariableLocation lhs (Reg rax)
    allocRegister lhs rax


    where
        sortReverse = sortOn (negate . snd)

handleLEA :: HasCallStack => Bool -> Variable -> ValueOper -> MachineCodeGeneratorM ()
handleLEA memaccess lhs oper = do
    tmpReg <- getFreeRegister
    let tmpLoc = Reg tmpReg
    markRegister tmpReg Occupied
    case oper of
        (LoadAddressLabel label) -> do
            emit $ Instruction2 "lea" (asMachine tmpLoc) (AddressLabel label)

         
        (LoadAddressOffset ptr off) -> do
            ptrLoc <- snd . head <$> loadAllWithConstraints [ptr] [tmpReg] True

            emit $ Instruction2 "lea"
                                (asMachine tmpLoc)
                                (Address (asMachine ptrLoc)
                                         Nothing
                                         (Just $ ImmediateInt (fromInteger off)))
        
        (LoadAddressArray arr size ind) -> do
            if isImmediate size then do
                let Immediate i = size
                markRegister tmpReg Free
                handleLEA memaccess lhs (LoadAddressOffset arr (toInteger i * ind))

            else do
                regs <- M.fromList <$> loadAllWithConstraints [arr, size] [] True
                
                let arrLoc  = regs ?! arr
                    sizeLoc = regs ?! size

                emit $ Instruction2 "lea" (asMachine tmpLoc)
                        (Address (asMachine arrLoc)
                                 (Just (asMachine sizeLoc, fromInteger ind))
                                 Nothing)
        _ -> error $ "Unknown operation: " ++ show (Variable lhs #= oper)
    
    if memaccess then do
        lhsLoc <- loadAvoiding (Variable lhs) [tmpLoc] True
        --lhsLoc <- getBestVariableLocation lhs >>= loadIfNotRegister lhs
        emit $ Instruction2 "mov" (asAddress lhsLoc) (asMachine tmpLoc)
        markRegister tmpReg Free
    else do

        addVariableLocation lhs tmpLoc

    

handleConditional :: HasCallStack => Operand -> CondOp -> Operand -> Label -> Label -> MachineCodeGeneratorM ()
handleConditional a cond b trueLabel falseLabel = do
    -- cond to nigdy AND, OR
    -- NOTE zachowanie dla stałych? chyba okej?
    aLoc <- getOperandLocation a >>= loadIfNotRegisterOp a >>= sustainIfUsedAgain a
    bLoc <- getOperandLocation b >>= sustainIfUsedAgain b


    emit $ instr2 "cmp" aLoc bLoc
    let jumpInstr = case cond of
            LT -> "jl"
            LE -> "jle"
            GT -> "jg"
            GE -> "jge"
            EQ -> "jz"
            NE -> "jnz"

    emit $ Instruction1 jumpInstr (ToLabel trueLabel)

    -- TODO to można pewnie wyoptymalizować
    emit $ Instruction1 "jmp"  (ToLabel falseLabel)


chooseInstruction :: HasCallStack => MachineCodeGeneratorM ()
chooseInstruction = do
    code <- gets (fst . head . currentCode)
    debugTrace 10 (altblueColor "instr: " ++ show code)
    case code of
        (ValueCode (Variable lhs) operation)   -> do
            instructionForOperation False lhs operation

        (ReferenceCode (Variable lhs) operation) -> do
            instructionForOperation True lhs operation

        (FlowCtrlCode fctrl) -> instructionForFlowControl fctrl
        (PhiFunction _ _) -> return ()
        _ -> error $ "Unknown code: " ++ show code

    where
        instructionForOperation ref lhs oper = case oper of
            (Binary a op b)     -> handleValBinOP ref lhs oper
            (Unary op a)        -> handleUnrOp lhs op a
            (CopyOf a)          -> handleCopyOf ref lhs a
            (LoadFrom a)        -> handleLoadFrom ref lhs a
            (Call label ops)    -> handleCall lhs (Left label) ops
            (CallReg addr ops)  -> handleCall lhs (Right addr) ops

            _ -> handleLEA ref lhs oper

        instructionForFlowControl fctrl = case fctrl of
            ReturnVoid  -> do
                emit (ToResolve "return")
            (Return op) -> do
                raxDesc <- gets ((?! rax) . registerUsage)
                if isOperandIn op raxDesc then do
                    emit (ToResolve "return")
                else do
                    loc <- getOperandLocation op
                    emit $ instr2 "mov" (Reg rax) loc
                    emit (ToResolve "return")
            (Jump label) -> emit $ Instruction1 "jmp" (ToLabel label)
            (InsertLabel label) -> emit $ Instruction0 label

            (ConditionalFull a c b l1 l2)   -> do
                handleConditional a c b l1 l2



generateInstructions :: HasCallStack => MachineCodeGeneratorM ()
generateInstructions = do
    code <- gets currentCode
    if null code then do
        debug ( altcyanColor "--End of code--")
        unifyEndState
        node <- gets currentNode
        genCode <- gets ((?! node) . generatedCode)
        debug ( altcyanColor "--reversing code--")
        let revCode = reverse genCode
        modify (\s ->  s{generatedCode = M.insert node revCode (generatedCode s)})
        return ()
    else do
        let (instr:rest) = code
        chooseInstruction
        removeDeadVariables
        modify (\s -> s{currentCode = rest,
                        aliveBeforeCurrentInst = snd instr})
        generateInstructions


{- Zaczynając od bloku wejściowego grafu:
    1. Generujemy instrukcje
    2. Zapisujemy stan zmiennych żywych na końcu bloku
    3. Informację o stanie tych zmiennych propagujemy wszystkim następnikom
    4. Każdy następnik propaguje tą informację jako wymóg do swoich poprzedników
   Graf przeglądamy w kolejności przepływu 
-}

-- TODO przekazać dostatecznie dużo parametrów, aby odczytać początkowy
-- stan zmiennych.
_simpleRegAlloc64 :: HasCallStack => Map Variable Variable -> MachineCodeGeneratorM ()
_simpleRegAlloc64 entryMappings = do
    debugTrace 0 ("_simpleRegAlloc64")
    graph <- gets flowGraph
    state <- get
    let startingNode = head (M.elems (M.filter (null . entries) graph))
        startingLabel = entryLabel startingNode
        -- args = map fst $ getPhiInfo (map fst $ instructions startingNode) []
        -- (regs, vars, moff) = inputFunctionArguments (length args) args

    -- Stara wartość -> nowa wartość
    let parametersOnly = M.filterWithKey (\k _ ->
                        case k of
                            (Parameter _) -> True
                            _ -> False
                        ) entryMappings
    -- Stary parametr -> nowy parametr
    let paramLocations = map (swap . first translateParamLocation)
                             (M.assocs parametersOnly)

    -- Nowy parametr -> lokalizacja
        regs = M.union (
                M.fromList
                $ map (\(var, Reg r) ->(r, makeRegisterDesc var (Reg r)))
                $ filter (isRegister . snd) paramLocations)
             allRegistersFree
        vars = M.map (S.singleton) (M.fromList paramLocations)

    debugTrace 1 ("First 5 lines of code:\n" ++ (unlines $ map show (take 5 (instructions startingNode))))

    debugTrace 10 ("Initial Registers:\n" ++ __prettyPrintRegisters regs)
    debugTrace 10 ("Initial Vars:\n" ++ __prettyPrintVariables vars)



    modify (\s -> s{initialNodeState = M.insert startingLabel (regs, vars) (initialNodeState s),
        maximalOffset = 0})

    void $ traverseBFS (neighbors graph) action S.empty startingLabel startingLabel
    -- NOTE zależnie od preambuły należy zmodyfikować
    -- NOTE offsety parametrów!
    where
        translateParamLocation param =
            let pIndex = getParamIndex param
            in
                if pIndex < toInteger x86_64ABIMaxRegisters then
                    Reg (registerNumber (x86_64ABIregisters !! fromInteger pIndex))
                else
                    Mem (x86_64ABIMaxRegisters - (fromInteger pIndex) - 2)

        getParamIndex (Parameter (Value i)) = i
        getParamIndex (Parameter (Reference i)) = i

        isRegister (Reg r) = True
        isRegister _ = False

        makeRegisterDesc var (Reg r) = RegDesc r Occupied (S.singleton var)


        getPhiInfo [] funcs = funcs
        getPhiInfo ((PhiFunction op mapping):rest) acc =
            getPhiInfo rest ((op, mapping):acc)
        getPhiInfo r@(_:rest) acc = acc


    -- Kolejność przeglądania
        neighbors cfg nodeLabel = S.toList (exits (cfg ?! nodeLabel))
        action parent node = do
            setupNextBlock parent node
            generateInstructions




traverseBFS neighbors action visited p n =
    if S.member n visited then return visited
    else do
        let newVisited = S.insert n visited
        action p n
        foldM (\vis new -> do
            traverseBFS neighbors action vis n new
            ) newVisited (neighbors n)

getPreamble :: Int -> Set Int -> ([MachineCode], [MachineCode], Int)
getPreamble offset registers =
    let
        preamble = [ Instruction0 "push rbp", Instruction0 "mov  rbp, rsp"]
        gentleRegs = S.fromList $ map registerNumber x86_64PreservedRegisters
        toPreserve = S.toList $ S.intersection registers gentleRegs
        toPreserveStr = map ((x86_64registers !!)) toPreserve
        wholeOffset = offset + length toPreserve + 1
        closestEven = if odd wholeOffset then offset else offset + 1
        stackAllocation = Instruction0 $ "sub rsp, " ++ show (8*closestEven)
        pushing = map (Instruction0 . ("push " ++ )) toPreserveStr
        popping = map (Instruction0 . ("pop " ++)) (reverse toPreserveStr)
    in
        if offset /= 0 then
            (pushing ++ preamble ++ [stackAllocation], popping, length toPreserve)
        else (pushing ++ preamble , popping, length toPreserve)

simpleRegisterAllocation :: HasCallStack => Map Variable Variable -> ControlFlowGraph -> IO (Map Integer (Label, [String]))
simpleRegisterAllocation entryMappings cfg = do
    debugTrace 0 "simpleRegisterAllocation"
    state <- execStateT (_simpleRegAlloc64 entryMappings) (emptyMCGState cfg)
    let entryNodeLabel = (setElemAt 0 . exits)
                       $ flowGraph state ?! SSA.dummyNodeLabel
    let ur = usedRegisters state

    let (preamble, pops, addOffset) = getPreamble (maximalOffset state) ur
    if null pops then do
        let what = "return"
            with = Instruction0 "leave\n\tret\n"
            subst = M.map (resolveCode what with) (generatedCode state)
        let retCodes = M.assocs $ M.insert entryNodeLabel
                                  (preamble ++ (subst ?! entryNodeLabel)) subst
        return $ M.fromList (toOutputMapping cfg retCodes)

    else do
        let exitLabel = "unified__" ++ entryNodeLabel ++ "_exit"
            what = "return"
            with = Instruction1 "jmp" (ToLabel exitLabel)
            subst1 = M.map (resolveCode what with) (generatedCode state)
            subst = M.map (map (adjustParameterOffsets (addOffset))) subst1
            retMap = M.fromList $ map (\(l,c) -> (position $ cfg ?! l, (l,c))) (M.assocs withPreamble)
            withPreamble = M.insert entryNodeLabel (preamble ++ (subst ?! entryNodeLabel)) subst
            mKey = toInteger (M.size cfg + 1000)
            exitCode = [Instruction0 "leave\n"] ++ pops ++ [Instruction0 "ret\n"]

        return $ M.map (second (map ((++"\n").show))) $ M.insert mKey (exitLabel, exitCode) retMap

    where
        toOutputMapping cfg = map (\(l,c) ->
            (position $ cfg ?! l,  (l, map ((++ "\n") . show) c)))
        

        adjustParameterOffsets :: Int -> MachineCode -> MachineCode
        adjustParameterOffsets i instr = case instr of
            (Instruction1 str ml)       -> Instruction1 str (adjust ml)
            (Instruction2 str ml1 ml2)  -> Instruction2 str (adjust ml1) (adjust ml2)
            (InstructionComment mc cmnt)-> InstructionComment (adjustParameterOffsets i mc) cmnt
            (Optional mc)   -> Optional (adjustParameterOffsets 1 mc)
            _ -> instr

            where adjust (StackOffset x) | x < 0     = StackOffset (x - i)
                                         | otherwise = StackOffset x
                  adjust mc = mc



prettyPrintCode :: CFGNode -> String
prettyPrintCode n = unlines $ (("\t" ++) . show) (InsertLabel (entryLabel n)-:):map (("\t" ++). myshow) (instructions n)
    where myshow (code, aset) = show code ++ "\t| alive: " ++ (show . S.toList)  aset

cfgShowCodeHuman :: ControlFlowGraph -> [String]
cfgShowCodeHuman cfg = _nodeShow (M.elems (M.filter (null . entries) cfg)) S.empty
    where
        _nodeShow :: [CFGNode] -> Set Label -> [String]
        _nodeShow [] _ = [""]
        _nodeShow (node:rest) visited =
            if S.member (entryLabel node) visited then
                _nodeShow rest visited
            else
                let ancestors = map (cfg ?!) $ S.toList (exits node)
                    newVisited = S.insert (entryLabel node) visited
                    codeToPrint = prettyPrintCode node
                    entryText = "alive at entry:" ++ (show . S.toList) (aliveEntry node) ++ "\n"
                in
                    (entryText ++ codeToPrint):_nodeShow (ancestors ++ rest) newVisited



resolveCode what with code = map (resolveInstruction what with) code
resolveInstruction :: String -> MachineCode -> MachineCode -> MachineCode
resolveInstruction what with inst | inst == ToResolve what = with
                                  | otherwise = inst
