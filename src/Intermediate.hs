{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Intermediate where
import Grammar.Abs hiding (Div, Mod)
import qualified Grammar.Abs as ABS
import Types
import qualified Types as T
import qualified Data.Map as M
import Common
import Error
import Data.Maybe (isNothing, fromJust, isJust, fromMaybe)
import Data.Traversable (for, forM)
import Control.Monad (when, forM_, unless, void, liftM, zipWithM, liftM2)
import Control.Monad.State (MonadState (put), get, gets, modify, MonadIO (liftIO))
import Control.Monad.RWS.Lazy (MonadReader(ask, reader, local), asks)
import Data.List (nub, sortOn)
import Data.Containers.ListUtils (nubOrd)
import Data.Char (toLower, isAscii)
import GHC.Stack (HasCallStack)
import Debug.Trace (trace)
import Debugging






store :: QuadCode -> GeneratorM ()
store newcode = do
    state <- get
    let oldcode = generatedCode state
    put $ state { generatedCode = newcode : oldcode }
    return ()

newLocation :: GeneratorM Location
newLocation = do
    state <- get
    let reg = regCounter state
    put $ state { regCounter = reg + 1 }
    return reg

newLocalValue :: GeneratorM Operand
newLocalValue = Variable . Local . Value <$> newLocation

newLocalReference :: GeneratorM Operand
newLocalReference = Variable . Local . Reference <$> newLocation

newLocalDereference :: GeneratorM Operand
newLocalDereference = Variable . Dereferenced . Local . Reference <$> newLocation

newLocalTypeOperand :: VarType -> GeneratorM Operand
newLocalTypeOperand vt = if isReference vt then newLocalReference
                         else newLocalValue

newFuncLabel :: String -> GeneratorM Label
newFuncLabel str = do
    if all isAscii str then
        return str
    else do
        state <- get
        let suffix = labelSuffix state
        put $ state { labelSuffix = suffix + 1 }
        return ("function_" ++ show suffix)

newLoopLabel :: GeneratorM Label
newLoopLabel = do
    suffix <- gets loopLabelSuffix
    modify (\s -> s {loopLabelSuffix = suffix + 1})
    return (".loop_" ++ show suffix)

newCondLabel :: GeneratorM Label
newCondLabel = do
    suffix <- gets condLabelSuffix
    modify (\s -> s {condLabelSuffix = suffix + 1})
    return (".if_" ++ show suffix)

newStringLabel :: GeneratorM Label
newStringLabel = do
    suffix <- gets stringLabelSuffix
    modify (\s -> s {stringLabelSuffix = suffix + 1})
    return ("str_" ++ show suffix)

constructMethodName :: Ident -> Ident -> Ident
constructMethodName mthd objname =
    Ident ("__object__" ++ getS objname ++ "_" ++ getS mthd)

constructVTALabel :: Ident -> Label
constructVTALabel objname =
    "VTA_" ++ getS objname ++ "_entries"



checkInheritance :: ClassName -> ClassName -> GeneratorM Bool
checkInheritance above below = do
    debugTrace 100 ("Is " ++ getS above ++ " super class of " ++ getS below)

    if above == below then return True else do
        belowInfo <- gets ((?! below) . objectsInfo)
        let superBelow = superClass belowInfo
        if isNothing superBelow then return False
        else do
            let Just super = superBelow
            if super == above then return True
            else checkInheritance above super


theSameType :: VarType -> VarType -> GeneratorM Bool
theSameType (Custom x) (Custom y) = checkInheritance x y
theSameType (Array (Custom x)) (Array (Custom y)) = checkInheritance x y
theSameType a b = return (a == b)


stdlib_h = [("printInt", Func {retType= Void, argTypes=[Int]} ,"__lat_builtin_printInt"),
            ("printString", Func {retType= Void, argTypes=[String]} ,"__lat_builtin_printString"),
            ("error", Func {retType= Void, argTypes=[]}, "__lat_builtin_makeError"),
            ("readInt", Func {retType= Int, argTypes=[]}, "__lat_builtin_readInt"),
            ("readString", Func {retType= String, argTypes=[]}, "__lat_builtin_readString")]

internalLibrary = buildMapping M.empty [] internal_library_functions
    where
          buildMapping :: M.Map String String -> [(String, FunType, String)] -> [(String, FunType)]
                          -> (M.Map String String, [(String, FunType, String)])
          buildMapping mapp acc [] = (mapp, acc)
          buildMapping mapp acc ((str,x):rest) =
            let prefixed = "__lat_builtin_" ++ str
                label = "__lat_builtin_" ++ str
            in
                buildMapping (M.insert str label mapp) ((prefixed, x, label):acc) rest
internallib_h = snd internalLibrary
internal_library_functions =
    [("strcat", Func {retType = String, argTypes=[String, String]}),
     ("heap_alloc", Func {retType = Array Void, argTypes=[Int]})]


getFunctionScope :: GeneratorM FunName
getFunctionScope = do
    scope <- asks currentScope
    return $ case scope of
        (FunctionScope   fname) -> fname
        (MethodScope _ _ fname) -> fname


getObjectScope :: GeneratorM (Maybe (ClassName, Operand), FunName)
getObjectScope = do
    scope <- asks currentScope
    return $ case scope of
        (MethodScope cname cop fname) ->  (Just (cname, cop), fname)
        (FunctionScope fname)     ->  (Nothing, fname)


isLocalScope :: VarName -> GeneratorM Bool
isLocalScope vname = do
    locmap <- asks varOpBind
    return $ isJust (M.lookup vname locmap)

-- Zmienne są trzymane lokalnie
getLocType :: Position -> VarName -> Bool -> GeneratorM Result
getLocType pos vname@(Ident str) asReference = do
    mObjName <- fst <$> getObjectScope
    locmap <- asks varOpBind
    prevmap <- asks lastVarBindOP
    let localVar = M.lookup vname locmap
        prevVar = M.lookup vname prevmap

    if isNothing mObjName then
        searchForVariable localVar prevVar notFoundError
    else do
        let Just (objName, objOper) = mObjName
        objectRecord <- gets ((?! objName) . objectsInfo)
        let isInObject = M.member vname (varOffsets objectRecord)

        if not isInObject then do
            searchForVariable localVar prevVar notFoundError
        else do
            searchForVariable localVar prevVar (checkInObject vname objName objOper)

    where
        searchForVariable localVar prevVar callback =
            maybe (
                maybe callback return prevVar
                ) return localVar

        checkInObject vname objName objOper =
            if asReference then do
                (vType, vOffset) <- getObjectVariable pos objName vname
                loc <- newLocalDereference
                store (loc #= LoadAddressOffset objOper vOffset)
                return (vType, loc)
            else do
                (vType, vOffset) <- getObjectVariable pos objName vname
                reg <- newLocalReference
                store (reg #= LoadAddressOffset objOper vOffset)
                val <- newLocalValue
                store (val #= LoadFrom reg // "." ++ getS vname)
                return (vType, val)



        notFoundError = makeError pos ("Variable " ++ str ++ " has not been defined.\n")


-- Informacje o klasach są trzymane globalnie
getObject :: BNFC'Position -> ClassName -> GeneratorM ObjectRecord
getObject pos cname = do
    objMap <- gets objectsInfo
    case M.lookup cname objMap of
        -- Nie ma takiego obiektu --
        Nothing         -> typeError pos
                            "Klasa obiektów tego typu nie została wcześniej zadeklarowana.\n"
        Just objInfo    -> return objInfo

getObjectVariable :: BNFC'Position -> ClassName -> VarName -> GeneratorM (VarType, Integer)
getObjectVariable pos cname vname = do
    objInfo <- getObject pos cname
    maybe (
        maybe wrongFieldError
            return (M.lookup vname (superClassOffsets objInfo))
        ) return (M.lookup vname (varOffsets objInfo))
    where
        wrongFieldError =
            fieldError pos ("Obiekt klasy " ++ getS cname
                            ++ " nie posiada pola o nazwie " ++ getS vname
                            ++ ".\n")

getObjectMethod :: BNFC'Position -> ClassName -> FunName -> GeneratorM (FunType, Integer)
getObjectMethod pos cname fname = do
    objInfo <- getObject pos cname
    let directMethod = M.member fname (methodTable objInfo)
        superMethod  = M.member fname (superClassMethodTable objInfo)
        has_method = superMethod || directMethod

    unless has_method
        (fieldError  pos "Obiekt nie posiada metody o podanej nazwie.\n")
    
    

    let (endFName, offset) = fromMaybe (superClassMethodTable objInfo ?! fname)
                                       (M.lookup fname (methodTable objInfo))

    ftype <- gets (fst . (?! endFName) . funcLabels)

    return (ftype, offset)

getTypeSize :: VarType -> GeneratorM Integer
getTypeSize Int         = return 8
getTypeSize Boolean     = return 8
getTypeSize String      = return 8
getTypeSize (Array _)   = return 8
getTypeSize (Custom classname) = return 8
-- do
--     objMap <- gets objectsInfo
--     case M.lookup classname objMap of
--         Nothing         -> willNeverHappen
--         Just objInfo    -> return (objectSize objInfo)

getExprIdent :: BNFC'Position -> Expr -> GeneratorM Ident
getExprIdent _ (EVar _ id) = return id
getExprIdent pos _         = fieldError pos ""


isCondExpr :: Expr -> Bool
isCondExpr (EAnd {}) = True
isCondExpr (EOr  {}) = True
isCondExpr (ERel {}) = True
isCondExpr _         = False

setReturnFlag :: BNFC'Position ->  GeneratorM ()
setReturnFlag pos= do
    debugTrace 0 ("Ustawienie flagi RF:\t" ++ show pos)
    modify (\s -> s {hasReturn= True, lastInstr= pos})

clearReturnFlag :: BNFC'Position -> GeneratorM ()
clearReturnFlag pos = do
    debugTrace 0 ("Czyszczenie flagi RF:\t"  ++ show pos)
    modify (\s -> s {hasReturn= False, lastInstr= pos})

returnFlag :: GeneratorM Bool
returnFlag = gets hasReturn

youreGodDamnRight :: Expr -> Bool
youreGodDamnRight (ELiteral _ (LTrue _ _)) = True
youreGodDamnRight _                        = False

youreGodDamnWrong :: Expr -> Bool
youreGodDamnWrong (ELiteral _ (LFalse _ _)) = True
youreGodDamnWrong _                         = False


-- Wyrażenia referencji --

genReferenceExpr :: Expr -> GeneratorM Result
genReferenceExpr expr = case expr of
    EVar pos id                 -> do
        (t, v) <- getLocType pos id True
        return (t, v)

    ELiteral pos lit                -> referenceError  pos
                                       "Literał nie jest modyfikowalną wartością.\n"
    EMethod pos _ _ _               -> referenceError  pos
                                       "Wynik wywołania metody nie jest modyfikowalną wartością.\n"
    ESelect pos object field        -> do
        (objT, objReg) <- genValueExpr object
        ident <- getExprIdent pos field
        case objT of
            Array at        ->  if ident == Ident "length" then referenceError
                                                                pos "Pole opisujące długość argumentu typu tablicowego nie jest modyfikowalną wartością.\n"
                                else fieldError
                                     pos "Argumenty typu tablicowego posiadają jedynie pole o nazwie 'length'.\n"
            Custom objName  -> do
                -- TODO zmienić na zmienną dereferencji!
                (vType, vOffset) <- getObjectVariable pos objName ident
                loc <- newLocalDereference
                store (loc #= LoadAddressOffset objReg vOffset)
                return (vType, loc)
            _               -> typeError
                               pos "Argument podanego typu nie posiada wewnętrznych pól.\n"


    EApp pos func args              -> referenceError  pos
                                       "Wynik wywołania funkcji nie jest modyfikowalną wartością.\n"
    ESubs pos arrayExpr index       -> do
        (at0, arrayReg) <- genValueExpr arrayExpr   -- Wyliczamy zmienną tablicową
        (it, ireg)  <- genValueExpr index           -- Wyliczamy indeks
        at <- typeCheckArraySubs pos at0 it         -- Sprawdzamy poprawność typów
        size <- getTypeSize at
        loc <- newLocalDereference  -- Przekazywana adres jest DEreferencją
        store (loc #= LoadAddressArray arrayReg ireg size)
        return (at, loc)

    ENeg pos expr                   -> arithmeticReferenceError pos
    ENot pos expr                   -> arithmeticReferenceError pos
    ENewArr pos arrType expr        -> referenceError  pos
                                       "Konstruktor 'new' nie występuje jako modyfikowalna wartość.\n"
    ENewObj pos basicType           -> referenceError  pos
                                       "Konstruktor 'new' nie występuje jako modyfikowalna wartość.\n"
    EBuiltinCast pos _ _            -> castError  pos
                                       "Rzutowanie na typy wbudowane jest niedozwolone.\n"
    EArrayCast pos _ _              -> castError  pos
                                       "Rzutowanie na typ tablicowy jest niedozwolone.\n"
    ECast pos objId expr            -> referenceError  pos
                                       "Wynik rzutowania nie jest modyfikowalną wartością.\n"
    EMul pos e1 (ABS.Times _) e2    -> arithmeticReferenceError pos
    EMul pos e1 (ABS.Div _)   e2    -> arithmeticReferenceError pos
    EMul pos e1 (ABS.Mod _)   e2    -> arithmeticReferenceError pos
    EAdd pos e1 (ABS.Plus _)  e2    -> arithmeticReferenceError pos
    EAdd pos e1 (ABS.Minus _) e2    -> arithmeticReferenceError pos
    ERel pos e1 relop e2            -> arithmeticReferenceError pos
    EAnd pos e1 e2                  -> arithmeticReferenceError pos
    EOr  pos e1 e2                  -> arithmeticReferenceError pos
    where arithmeticReferenceError pos = referenceError pos "Wynik wyrażenia arytmetycznego nie jest modyfikowalną wartością.\n"
-- Wyrażenia wartości --

genValueExpr :: Expr -> GeneratorM Result
genValueExpr expr = case expr of
    EVar pos id                 -> do
        (t, v) <- getLocType pos id False
        return (t, v)

    ELiteral pos lit            -> case lit of
        LInt _ i    -> return (Int,     Immediate $ fromInteger i)
        LTrue _ _   -> return (Boolean, Immediate 1)
        LFalse _ _  -> return (Boolean, Immediate 0)
        LNULL _ _   -> return (Void,    Immediate 0)
        LString _ str -> do
            sl <- getStaticStringLabel str
            reg <- newLocalReference
            store (reg #= LoadAddressLabel sl)
            return (String, reg)
        LChar _ _   -> makeCustomError "Unrecognized Type" pos "Typ znakowy jest niewspierany.\n"

    EMethod pos object fname args   -> do
        (objT, objV) <- genValueExpr object
        argVals <- mapM genValueExpr args
        case objT of
            Custom objName      -> do
                let methodName = constructMethodName fname objName
                    firstArg = Variable (Parameter (Reference 0))

                (funtype, methodOffset) <- getObjectMethod pos objName fname
                retT <- typeCheckFunctionCall pos funtype (map fst argVals)

                -- TODO poprawić obiekty!
                -- vtab := adres tablic metod wirtualnych
                vTabAddr <- newLocalReference
                store (vTabAddr #= LoadAddressOffset objV objectVTAOffset // "vTable field address")

                vtab <- newLocalReference
                store (vtab #= LoadFrom vTabAddr // "vTable field value")

                -- mthd := adres metody wirtualnej
                mthdAdd <- newLocalReference
                store (mthdAdd #= LoadAddressOffset vtab (methodOffset*8) // "virtual method offset address")

                mthdRel <- newLocalReference
                store (mthdRel #= LoadFrom mthdAdd // "virtual method offset (rel vTable)")

                mthd <- newLocalReference
                store (mthd #= Binary mthdRel Add vtab // "virtual method full address")

                let callArgs = objV : map snd argVals
                -- ret := wynik wywołania o typie retT
                ret <- newLocalValue
                store (ret #= CallReg mthd callArgs // "virtual call")
                return (retT, ret)


            _NotAnObject        -> typeError pos "Argument podanego typu nie posiada wewnętrznych metod.\n"

    -- Tylko pola wartościowane --
    ESelect pos object field        -> do
        (objT, objV) <- genValueExpr object
        ident <- getExprIdent pos field
        case objT of
            Array at    ->
                -- Tablice mają tylko jedno pole --
                if ident /= Ident "length" then fieldError
                                                pos "Argumenty typu tablicowego posiadają jedynie pole o nazwie 'length'.\n"
                else do
                    tmp <- newLocalReference
                    store (tmp #= LoadAddressOffset objV arrayLengthOffset)
                    val <- newLocalValue
                    store (val #= LoadFrom tmp // ".length")
                    return (Int, val)
            -- Obiekt --
            Custom objName  -> do
                (vType, vOffset) <- getObjectVariable pos objName ident
                reg <- newLocalReference
                store (reg #= LoadAddressOffset objV vOffset)
                val <- newLocalValue
                store (val #= LoadFrom reg // "." ++ getS ident)
                return (vType, val)
            -- Coś innego --
            _               -> typeError
                               pos "Argument podanego typu nie posiada wewnętrznych pól.\n"

    EApp pos func args              -> do
        finfo <- gets (M.lookup func . funcLabels)
        if isNothing finfo then
            makeCustomError "Name Error" pos "Funkcja o podanej nazwie nie istneje.\n"
        else do
            let Just (ftype, label) = finfo
            argVals <- mapM genValueExpr args
            retT <- typeCheckFunctionCall pos ftype (map fst argVals)
            ret <- newLocalValue
            store (ret #= Call label (map snd argVals))
            return (retT, ret)

    e@(ESubs pos arrayExpr index)   -> do
        (at, reg) <- genReferenceExpr e -- reg := address of specified cell
        val <- newLocalValue
        store (val #= LoadFrom reg)     -- load from cell
        return (at, val)


    ENeg pos expr                   -> genUnrOp pos expr Neg
    ENot pos expr                   -> genUnrOp pos expr Not
    ENewArr pos (AType _ at) expr   -> do
        debugTrace 0 "Alokowanie tablicy na stercie nie jest jeszcze zaimplementowane.\n"
        let atype = translateType at
        case atype of
            Array _     -> makeCustomError "Array Type Error" pos "Nie można tworzyć tablicy tablic.\n"
            _           -> do
                (t, o) <- genValueExpr expr
                when (t /= Int) $ typeError pos "Rozmiar tablicy musi być typu całkowitoliczbowego.\n"

                let heap_alloc = fst internalLibrary ?! "heap_alloc"
                reg <- newLocalValue
                size <- getTypeSize atype

                store (reg #= Binary o Mul (Immediate $ fromInteger size))

                arrAdr <- newLocalReference
                store (arrAdr #= Call heap_alloc [reg])
                arrLenAdr <- newLocalReference
                store (arrLenAdr #= LoadAddressOffset arrAdr arrayLengthOffset)
                store (arrLenAdr @= CopyOf o)

                return (Array atype, arrAdr)



    ENewObj pos basicType           -> do
        debugTrace 0 "Alokowanie nowego obiektu na stercie nie jest jeszcze zaimplementowane.\n"
        let objType = translateBasicType basicType
        case objType of
            Custom name     -> do
                objInfo <- getObject pos name
                -- Zaalokować odpowiednio dużo miejsca na stercie
                -- Wrzucić pod offset (-1) adres vTable tego obiektu
                let heap_alloc = fst internalLibrary ?! "heap_alloc"

                objAdr <- newLocalReference
                store (objAdr #= Call heap_alloc [Immediate (fromInteger $ objectSize objInfo)])
                vTabAddr <- newLocalDereference
                store (vTabAddr #= LoadAddressOffset objAdr objectVTAOffset // "Virtual Method Table field")
                store (vTabAddr @= LoadAddressLabel (virtualTableLabel objInfo) // "Address load")
                return (objType, objAdr)
            _               -> makeCustomError "Constructor Error" pos "Operator 'new' nie może być użyty do utworzenia obiektu typu wbudowanego.\n"


    EBuiltinCast pos _ _            -> castError  pos
                                       "Rzutowanie na typy wbudowane jest niedozwolone.\n"
    EArrayCast pos _ _              -> castError  pos
                                       "Rzutowanie na typ tablicowy jest niedozwolone.\n"
    ECast pos objId expr            -> case expr of
        ELiteral _ (LNULL _ _)  -> do
            objInfo <- getObject pos objId
            reg <- newLocalReference
            store (reg #= CopyOf nullPointer)
            return (Custom objId, reg)
        _ -> willNeverHappen

    EMul pos e1 (ABS.Times _) e2    -> genBinOp pos e1 e2 Mul
    EMul pos e1 (ABS.Div _)   e2    -> genBinOp pos e1 e2 Div
    EMul pos e1 (ABS.Mod _)   e2    -> genBinOp pos e1 e2 Mod
    EAdd pos e1 (ABS.Plus _)  e2    -> genBinOp pos e1 e2 Add
    EAdd pos e1 (ABS.Minus _) e2    -> genBinOp pos e1 e2 Sub
    e@(ERel pos e1 relOp e2)        -> genCondOp pos e
    e@(EAnd pos e1 e2)              -> genCondOp pos e
    e@(EOr  pos e1 e2)              -> genCondOp pos e




-- Function / method call
typeCheckFunctionCall :: BNFC'Position -> FunType -> [VarType] -> GeneratorM VarType
typeCheckFunctionCall pos (Func retT fArgsT) inArgsT = do
    paramsOK <- and <$> zipWithM parameterEquivalent fArgsT inArgsT

    if paramsOK && length fArgsT == length inArgsT then
        return retT
    else
        typeError pos ("Parametry wywołania są niepoprawnego typu.\n"
                        ++ "Oczekiwano: " ++ show fArgsT ++ "\n"
                        ++ "Przekazano: " ++ show inArgsT ++ "\n")

    where
        --                     Declaration Argument
        parameterEquivalent :: VarType -> VarType -> GeneratorM Bool
        parameterEquivalent (Custom x) (Custom y) = checkInheritance x y
        parameterEquivalent a b = return (a == b)


-- genCallOp :: BNFC'Position -> Expr -> [Expr] -> GeneratorM Result
typeCheckArraySubs :: BNFC'Position -> VarType -> VarType -> GeneratorM VarType
typeCheckArraySubs pos at it = do
    t <- case at of
        Array at  -> return at
        _         -> typeError pos ""
    if it /= Int then
        typeError pos ""
    else
        return t


-- Conditional Operations
typeCheckCondOp :: BNFC'Position -> VarType -> VarType -> CondOp -> GeneratorM ()
typeCheckCondOp pos t1 t2 condop
    | condop `elem` [AND, OR]   = unless (t1 == Boolean && t2 == Boolean) $
                                    typeError pos "Argumenty wyrażenia logicznego muszą być typu logicznego.\n"
    | condop `elem` [T.EQ, T.NE]= unless (equivalenceCapable t1 t2) $
                                    typeError pos "Argumenty podanych typów są nie przyrównywalne.\n"
    | otherwise                 = unless (t1 == t2 && comparable t1) $
                                    typeError pos "Argumenty podanych typów są nie prównywalne.\n"

genCondOp :: BNFC'Position -> Expr -> GeneratorM Result
genCondOp pos expr = do
    trueL <- newCondLabel
    falseL <- newCondLabel
    skipL <- newCondLabel

    reg <- newLocalValue

    genCond pos expr trueL falseL

    store (InsertLabel trueL -:)
    store (reg #= CopyOf (Immediate 1))
    store (Jump skipL -:)

    store (InsertLabel falseL -:)
    store (reg #= CopyOf (Immediate 0))

    store (InsertLabel skipL -:)
    return (Boolean, reg)

genCond :: BNFC'Position -> Expr -> Label -> Label -> GeneratorM ()
genCond p expr trueL falseL = case expr of
    (ENot pos e)        -> genCond pos e falseL trueL

    (EAnd pos e1 e2)    -> do
        midL <- newCondLabel
        genCond pos e1 midL falseL
        store (InsertLabel midL -:)
        genCond pos e2 trueL falseL

    (EOr pos e1 e2)     -> do
        midL <- newCondLabel
        genCond pos e1 trueL midL
        store (InsertLabel midL -:)
        genCond pos e2 trueL falseL

    (ERel pos e1 op e2)    -> do
        (t1, r1) <- genValueExpr e1
        (t2, r2) <- genValueExpr e2
        let condOp = translateRelOp op
        typeCheckCondOp pos t1 t2 condOp
        store (ConditionalFull r1 condOp r2 trueL falseL -:)
        -- store (Jump falseL -:)

    _                   -> do
        (t, r) <- genValueExpr expr
        unless (t == Boolean) $
            typeError p "Argumenty wyrażenia logicznego muszą być typu logicznego."
        store (ConditionalFull r Types.EQ (Immediate 1) trueL falseL -:)
        -- store (Jump falseL -:)

    {-- 
    (EVar pos id)       -> do
        (t, r) <- getLocType pos id

        unless (t == Boolean) $
            typeError p "!! Argumenty wyrażenia logicznego muszą być typu logicznego."

        store (ConditionalFull r Types.EQ (Immediate 1) trueL -:)
        store (Jump falseL -:)

    _   ->  typeError p $ "Argumenty wyrażenia logicznego muszą być typu logicznego." ++ show expr
    --}



-- Binary Operations 
typeCheckBinOp :: BNFC'Position -> VarType -> VarType -> BinOp -> GeneratorM VarType
typeCheckBinOp pos t1 t2 _ = do
    if t1 /= t2 || t1 == Void then
        typeError pos "Typy argumentów w wyrażeniu są niezgodne ze sobą.\n"
    else
        return t1

calcImmediateBinOp :: Int -> BinOp -> Int -> Int
calcImmediateBinOp i1 binop i2 = case binop of
    Add -> i1 + i2
    Sub -> i1 - i2
    Mul -> i1 * i2
    Div -> i1 `div` i2
    Mod -> i1 `mod` i2

genBinOp :: BNFC'Position -> Expr -> Expr -> BinOp -> GeneratorM Result
genBinOp pos e1 e2 binop = do
    (t1, op1) <- genValueExpr e1
    (t2, op2) <- genValueExpr e2
    tres <- typeCheckBinOp pos t1 t2 binop

    unless (allowedOperation tres binop) $
        makeCustomError "Operation Error" pos "Typy argumentów w wyrażeniu nie wspierają podanej operacji."
    
    let strcat = (fst internalLibrary) ?! "strcat"
    reg <- case tres of
        
        String  -> do
            reg <- newLocalTypeOperand tres
            store (reg #= Call strcat [op1, op2] // "String concatenation!")
            return reg
        _       -> do
            if isImmediate op1 && isImmediate op2 then do
                let Immediate i1 = op1
                    Immediate i2 = op2
                    result = calcImmediateBinOp i1 binop i2
                return (Immediate result)
            else do
                reg <- newLocalTypeOperand tres
                store (reg #= Binary op1 binop op2)
                return reg
    return (tres, reg)
    where
        allowedOperation Int _ = True
        allowedOperation Boolean _ = False
        allowedOperation String Add = True
        allowedOperation String _ = False
        allowedOperation (Custom _) _ = False
        allowedOperation (Array _) _ = False

-- Unary Operations
checkUnrOp :: BNFC'Position -> VarType -> UnrOp -> GeneratorM VarType
checkUnrOp pos t1 oper = case oper of
        Not     ->  if negatable t1 then
                        return t1
                    else
                        typeError pos "Wyrażenie tego typu nie posiada elementu przeciwnego.\n"
        Neg     ->  if invertible t1 then
                        return t1
                    else
                        typeError pos "Wyrażenia tego typu nie można zaprzeczyć.\n"

genUnrOp :: BNFC'Position -> Expr -> UnrOp -> GeneratorM Result
genUnrOp pos expr unrop = do
    (t, op) <- genValueExpr expr
    tres <- checkUnrOp pos t unrop

    reg <- newLocalValue
    -- Jeżeli znamy wartośc to możemy ją odwrócic
    if isImmediate op then do
        let Immediate i = op
        case unrop of
            Neg -> store (reg #= CopyOf (Immediate (-i)))
            Not -> if i > 0 then store (reg #= CopyOf (Immediate 0))
                            else store (reg #= CopyOf (Immediate 1))
    else do
        store (reg #= Unary unrop op)

    return (tres, reg)



                    ---------------------------------------------
                    -- Przetwarzanie poszczególnych instrukcji --
                    ---------------------------------------------

getStaticStringLabel :: String -> GeneratorM Label
getStaticStringLabel str = do
    ss <- gets staticStrings
    let search = M.lookup str ss
    if isNothing search then do
        newSL <- newStringLabel
        modify (\s -> s{staticStrings = M.insert str newSL (staticStrings s)})
        return newSL
    else let Just label = search in return label
nullPointer = Immediate 0

makeDefaultValue :: VarType -> GeneratorM Operand
makeDefaultValue vtype = case vtype of
    Int     -> return (Immediate 0)
    Boolean -> return (Immediate 0)
    String  -> do
        sl <- getStaticStringLabel ""
        reg <- newLocalReference
        store (reg #= LoadAddressLabel sl)
        return reg
    Custom obj  -> return nullPointer
    Array atype -> return nullPointer
    Void    -> willNeverHappen

genStatements :: [Stmt] -> GeneratorM ()
genStatements [] = return ()
genStatements (stmt:rest) = case stmt of
    Empty pos   -> genStatements rest

    BStmt pos (Block _ instrs)    -> do
        local movBindings (genStatements instrs)
        blockReturned <- returnFlag
        -- If block ended with return, we dont need to calculate anything more
        unless blockReturned (genStatements rest)
        where
            movBindings env = env {lastVarBindOP= M.union (varOpBind env) (lastVarBindOP env), varOpBind= M.empty}

    Decl pos declType items         -> do
        let t = translateType declType
        processDeclarations t items rest
        where
            processDeclarations t [] instrs = genStatements instrs
            processDeclarations t (item:decls) instrs = do
                env <- ask
                case item of
                    NoInit _ id     -> do
                        reg <- if isReference t then newLocalReference
                               else newLocalValue

                        debugTrace 0 "Inicjalizacja wartości zmiennej"
                        defaultOP <- makeDefaultValue t
                        store (reg #= CopyOf defaultOP // getS id ++ " ~ " ++ show reg ++ " (default value)")
                        proceedFurther id t reg decls instrs

                    Init _ id expr  -> do
                        (newt, v) <- genValueExpr expr
                        
                        reg <- if isReference t then newLocalReference
                               else newLocalValue
                        store (reg #= CopyOf v // getS id ++ " ~ " ++ show reg)

                        typeOK <- theSameType t newt
                        unless typeOK $
                            typeError pos (show t ++ " =/= " ++ show newt ++"\tPrzypisanie wymaga zmiennych tego samego typu.\n")
                        proceedFurther id t reg decls instrs

            proceedFurther ident t reg decls instrs = do
                varBinds <- asks varOpBind
                when (isJust $ M.lookup ident varBinds) $
                    makeCustomError "Multiple Declarations" pos "Zmienna została już wcześniej zadeklarowana"

                local (insertLocalVar ident t reg)
                      (processDeclarations t decls instrs)

            insertLocalVar name vtype reg env =
                env {varOpBind = M.insert name (vtype, reg) (varOpBind env)}




    Ass pos refExpr valExpr         -> do
        (tr, or) <- genReferenceExpr refExpr
        (tv, ov) <- genValueExpr valExpr

        typesOK <- theSameType tr tv
        if not typesOK then typeError pos (show tr ++ " =/= " ++ show tv ++"\tPrzypisanie wymaga zmiennych tego samego typu.\n")
        else if isDereference or then
            store (or @= CopyOf ov )
        else
            store (or #= CopyOf ov)

        clearReturnFlag pos
        genStatements rest

        -- clearReturnFlag pos
        -- if tr /= tv then typeError pos (show tr ++ " =/= " ++ show tv ++"\tPrzypisanie wymaga zmiennych tego samego typu.\n")
        -- else if isPointer or then do
        --     store (or @= CopyOf ov )
        --     genStatements  rest
        -- else do
        --     reg <- newLocalValue
        --     store (reg #= CopyOf ov // show ov ++ " -> " ++ show reg)
        --     vname <- getExprIdent pos refExpr
        --     locality <- isLocalScope vname
        --     local (changeVariableLocation locality vname (tr, reg))
        --         (genStatements rest)

        -- where changeVariableLocation locality vn (t, o) env = 
        --         if locality then
        --             env{varOpBind = M.insert vn (t,o) (varOpBind env)}
        --         else
        --             env{lastVarBindOP = M.insert vn (t,o) (lastVarBindOP env)}


    Incr pos refExpr                -> do
        (t, o) <- genReferenceExpr refExpr
        if t /= Int then typeError pos "Można jedynie inkrementować wartości zmiennych typu liczbowego.\n"
        else
            if isDereference o then do
                tmp <- newLocalValue
                store (tmp #= LoadFrom o)
                store (o @= Binary tmp Add (Immediate 1))
            else do
            -- SSA zajmiemy się póżniej --
                store (o #= Binary o Add (Immediate 1))

        clearReturnFlag pos
        genStatements  rest

    Decr pos refExpr                -> do
        (t, o) <- genReferenceExpr refExpr
        if t /= Int then typeError pos "Można jedynie dekrementować wartości zmiennych typu liczbowego.\n"
        else
            -- SSA zajmiemy się póżniej --
            if isDereference o then do
                tmp <- newLocalValue
                store (tmp #= LoadFrom o)
                store (o #= Binary tmp Sub (Immediate 1))
            else do
                store (o #= Binary o Sub (Immediate 1))


        clearReturnFlag pos
        genStatements  rest

    Ret pos valExpr                 -> do
        (t, o) <- genValueExpr valExpr

        fname <- getFunctionScope
        ftype <- gets (retType . fst . (?! fname) . funcLabels )
        when (t /= ftype) $ typeError pos "Typ przekazywanej wartości jest inny niż typ wynikowy funkcji.\n"

        store (Return o -:)
        setReturnFlag pos
        -- genStatements rest

    VRet pos                        -> do

        fname <- getFunctionScope
        ftype <- gets (retType . fst . (?! fname) . funcLabels )
        when (ftype /= Void) $ typeError pos "Typ przekazywanej wartości jest inny niż typ wynikowy funkcji.\n"

        store (ReturnVoid -:)
        setReturnFlag pos
        -- genStatements rest

    Cond pos condExpr instr         -> do
        if youreGodDamnWrong condExpr then do
            debugTrace 0 "God damn wrong"
            genStatements rest
        else if youreGodDamnRight condExpr then do
            debugTrace 0 "God damn right"
            genStatements [instr]
            genStatements rest
        else do
            trueL <- newCondLabel
            skipL <- newCondLabel

            genCond pos condExpr trueL skipL
            store (InsertLabel trueL -:)
            genStatements [instr]
            store (InsertLabel skipL -:)

            clearReturnFlag pos
            genStatements  rest




    CondElse pos condExpr instTrue instFalse    -> do
        if youreGodDamnRight condExpr then do
            debugTrace 0 "God damn right"
            genStatements [instTrue]
            -- Nie trzeba obliczać ścieżki dla false
        else if youreGodDamnWrong condExpr then do
            -- Nie trzeba obliczać ścieżki dla true
            debugTrace 0 "God damn wrong"
            genStatements [instFalse]
        else do
            clearReturnFlag pos

            falseL <- newCondLabel
            trueL  <- newCondLabel
            endL  <- newCondLabel

            -- WARNING usunięcie komentarzy psuje działanie
            -- WARNING generacji kodu maszynowego - pewnie coś z makeCFG!

            genCond pos condExpr trueL falseL
            store (InsertLabel falseL -:)   -- .false:
            genStatements [instFalse]       -- <code>
            ret2 <- returnFlag
            store ((Jump endL -:) // trueL ++ " branch skip")            -- goto .end

            clearReturnFlag pos
            store (InsertLabel trueL -:)    -- .true
            genStatements [instTrue]        -- <code>
            ret1 <- returnFlag
            store ((InsertLabel endL -:) // trueL ++ " branch skip label")     -- .end

            -- Jeżeli obie gałęzie zakończyły się returnem
            -- to nie wymagamy dalszego returna
            if ret2 && ret1 then setReturnFlag pos else clearReturnFlag pos

        rf <- returnFlag -- Każda wybierana gałąź kończy się returnem
        unless rf $ do
            debugTrace 0 "Była odnoga niekończąca się!"
            genStatements  rest

    While pos condExpr instr        -> do
        unless (youreGodDamnWrong condExpr) $ do
            bodyL <- newLoopLabel
            skipL <- newLoopLabel
            condL <- newLoopLabel               --------------------------------
            store (Jump condL -:)               --        goto .cond
            store (InsertLabel bodyL -:)        -- .body:
            genStatements [instr]               --        <loop body>
            store (InsertLabel condL -:)        -- .cond:
            genCond pos condExpr bodyL skipL    --        <cond code>
            store (InsertLabel skipL -:)        --        if cond goto .body
                                                --------------------------------
        clearReturnFlag pos
        genStatements  rest

    ForEach pos arrT@(AType _ t) ittId arrId instr       -> do
        (at, ar) <- getLocType pos arrId False
        -- len := ar.length
        (it, len) <- genValueExpr (ESelect pos (EVar pos arrId) (EVar pos (Ident "length")))
        let Array elemType = at

        bodyL <- newLoopLabel
        condL <- newLoopLabel
        exitL <- newLoopLabel

        size <- getTypeSize elemType
        i <- newLocalValue
        p <- newLocalReference
        x <- newLocalValue

        store (i #= CopyOf (Immediate 0)        // "_i  := 0")
        store (Commented (Jump condL -:)           "jmp .cond")
        store (Commented (InsertLabel bodyL -:)    ".body")
        store (p #= LoadAddressArray ar i size  // "p := "++ getS arrId ++" + _i * size")
        store (x #= LoadFrom p                  //  getS ittId ++ " := *p")
        local (insertLocalVar ittId elemType x) --        <loop body with x>
              (genStatements [instr])           --
        store (i #= Binary i Add (Immediate 1)  //        "_i++")
        store (InsertLabel condL -:)            -- .cond:
                                                -- if (i < ar.length) goto .body
        store (ConditionalFull i Types.LT len bodyL exitL -:)
        store (InsertLabel exitL -:)

        clearReturnFlag pos
        genStatements  rest
        where insertLocalVar name vtype reg env =
                env {varOpBind = M.insert name (vtype, reg) (varOpBind env)}

    SExp pos expr                   -> do
        void $ genValueExpr expr
        clearReturnFlag pos
        genStatements  rest

    where
        checkIfBoolean pos t = when (t /= Boolean) $ typeError pos "Wymagane jest wyrażenie warunkowe typu logicznego.\n"


                    ------------------------------------
                    -- Przetwarzanie wysoko poziomowe --
                    ------------------------------------


                              -- Funkcje --

_loadParameters i m [] = m
_loadParameters i m ((at, an):rest) =
    _loadParameters (i+1) (M.insert an (at, makeOperand at i) m) rest
    where
        makeOperand atype i =
            if isReference atype then Variable (Parameter (Reference i))
                                 else Variable (Parameter (Value i))

loadParameters :: [Arg] -> M.Map VarName Result
loadParameters args = _loadParameters 0 M.empty (map translateArg args)
    where
        translateArg (Arg _ argT name) = (translateType argT, name)


saveCodeAndReset :: FunName -> GeneratorM ()
saveCodeAndReset fname = do
    debugTrace 0 ("Saving code of function " ++ getS fname)
    state <- get
    let newFuncCodeEntry = M.insert fname (reverse $ generatedCode state)
                                          (functionsCode state)
    modify (\s -> s{functionsCode = newFuncCodeEntry,
               generatedCode = [],
               lastInstr = Just (0,0),
               hasReturn = False,
               regCounter = 0,
               maxRegCounter = max (regCounter s) (maxRegCounter s)})

checkReturnFlag :: FunName -> VarType -> GeneratorM ()
checkReturnFlag fname fRetType = do
    rf <- returnFlag
    unless (fRetType == Void || rf) $ do
        let Ident fn = fname
        debugTrace 0 ("Function " ++ fn ++ " has return type: " ++ show fRetType)
        lastPos <- gets lastInstr
        makeCustomError "Control Flow Error" lastPos "Ostatnia instrukcja wewnątrz funkcji przekazującej wartość nie jest instrukcją powrotu.\n"

genFunction :: Function -> GeneratorM ()
genFunction (FunctionDef pos _ fname args (Block _ instrs)) = do
    -- Sprawdzanie unikalności nazwy funkcji jest wykonywane wcześniej --

    fRetType <- gets (retType . fst . (?! fname) . funcLabels)
    -- Wszystkie zmienne lokalne i statyczne są wyzerowane

    -- Generujemy kod dla funkcji
    local (\e -> e {varOpBind= loadParameters args,
                    currentScope= FunctionScope fname}) $ do
        clearReturnFlag pos

        genStatements instrs

        checkReturnFlag fname fRetType

    -- Zapisujemy wygenerowany kod funkcji i resetujemy statyczne wartości
    saveCodeAndReset fname


checkFunctionDefinition :: Function -> GeneratorM Label
checkFunctionDefinition (FunctionDef pos typ fname args body) = do
    alreadyExists <- gets (isJust . M.lookup fname . funcLabels)
    when alreadyExists $
        makeCustomError "Name Error" pos "Funkcja o podanej nazwie już istnieje.\n"

    let returnType = translateType typ
        typeNamePairs = map translateArg args
    -- Czy argumenty mają unikalne nazwy? --
    if length args /= length (nubOrd (map snd typeNamePairs)) then
        makeCustomError "Parameter Error" pos "Parametry funkcji muszą mieć unikalne nazwy.\n"
    else do
        -- Dodajemy funkcję na listę istniejących
        let Ident fstr = fname
        label <- newFuncLabel fstr
        let retval = (Func {retType= returnType, argTypes= map fst typeNamePairs}, label)
        modify (\s -> s {funcLabels= M.insert fname retval (funcLabels s)})
        return label

    where
    translateArg (Arg _ argT name) = (translateType argT, name)

                            -- Obiekty --

-- Tworzenie nowej tablicy metod wirtualnych
-- 1. Utwórz nową vTable jeżeli obiekt nie dziedziczy
-- 2. W.p.p. skopiuj vTable przodka
buildVMT :: ObjName -> Maybe ObjName -> GeneratorM ()
buildVMT objName superClass = do
    state <- get
    let vmtLabel = constructVTALabel objName
    objr <- gets ((?! objName) . objectsInfo)
    let newObjectsInfo = M.insert objName objr{virtualTableLabel = vmtLabel}
                                                         (objectsInfo state)
    objNewTable <- if isNothing superClass then do
                        return $ M.insert objName M.empty (vTablesInfo state)
                      else do
                        let Just superName = superClass
                        superTable <- gets ((?! superName) . vTablesInfo)
                        return $ M.insert objName superTable (vTablesInfo state)
    debugTrace 100 ("new Virtual Method Table of class " ++ getS objName ++ ":\n" ++ show objNewTable)
    modify (\s -> s{vTablesInfo = objNewTable,
                    objectsInfo = newObjectsInfo})

loadParametersWithObject :: ClassName -> [Arg] -> M.Map VarName Result
loadParametersWithObject objName args =
    let casualArguments = _loadParameters 1 M.empty (map translateArg args)
    in
        M.insert (Ident "self")
                 (Custom objName, Variable (Parameter (Reference 0)))
                 casualArguments
    where
        translateArg (Arg _ argT name) = (translateType argT, name)

genMethod :: ClassName -> Function -> GeneratorM ()
genMethod objName (FunctionDef pos _ methodName args (Block _ instrs)) = do
    -- let methodName = constructMethodName fname objName
    mRetType <- gets (retType . fst . (?! methodName) . funcLabels)
    let firstArgument = Variable (Parameter (Reference 0))
    local (\e -> e{varOpBind = loadParametersWithObject objName args,
                   currentScope = MethodScope objName firstArgument methodName}) $ do
        clearReturnFlag pos

        genStatements instrs

        checkReturnFlag methodName mRetType

    saveCodeAndReset methodName


-- Dodawanie zmiennej do obiektu
buildObject :: ObjName -> Decl -> GeneratorM ()
buildObject objName (DeclareVar p declType vars) = do
    let t = translateType declType
    forM_ vars (addVariable objName t)
    where
        addVariable objName vt vid = do
            record <- getObject p objName
            let alreadyExists = M.member vid $ varOffsets record

            when alreadyExists $
                makeCustomError "Name Error" p ("Zmienna wewnętrzna obiektu klasy" ++ getS objName ++ " została wcześniej zadeklarowana.")

            varSize <- getTypeSize vt
            let lastVO = build_lastVO record
                newv = M.insert vid (vt, lastVO) (varOffsets record)
                newSize = objectSize record + varSize

                newr = record{build_lastVO = lastVO + varSize,
                              varOffsets   = newv,
                              objectSize   = newSize}
            modify (\s ->
                s {objectsInfo= M.insert objName newr (objectsInfo s)})

-- Dodawanie metody do obiektu
-- TODO sprawdzenie czy metoda nie została zdefiniowana w nadklasie!
buildObject objName (DeclareFun p (FunctionDef pos typ fname args body)) = do
    record <- getObject p objName
    let alreadyExists = M.member fname $ methodTable record
        definedInSuper = M.member fname $ superClassMethodTable record

    when alreadyExists $
        makeCustomError "Name Error" p ("Metoda wewnętrzna klasy" ++ getS objName ++ " została wcześniej zadeklarowana.")


    let methodName = constructMethodName fname objName
    methodLabel <- checkFunctionDefinition (FunctionDef pos typ methodName args body)
    genMethod objName (FunctionDef pos typ methodName args body)

    objInfo <- gets objectsInfo
    record <- getObject p objName
    
    vtInfo <- gets vTablesInfo
    let lastMO = build_lastMO record
    let objVT = M.findWithDefault M.empty objName vtInfo
    -- Dodajemy do indeksu
    let (newRecord, newVTEntry) =
            if definedInSuper then
                let (oldFun, offset) = superClassMethodTable record ?! fname
                    newEntry = (methodName, offset)
                    newm     = M.insert fname newEntry (superClassMethodTable record)
                in
                    (
                        record{superClassMethodTable = newm},
                        M.insert offset methodLabel objVT
                    )
            else
                let lastMO = build_lastMO record
                    newm   = M.insert fname (methodName, lastMO) (methodTable record)
                in
                (
                    record{build_lastMO = lastMO + 1, methodTable  = newm},
                    M.insert lastMO methodLabel objVT
                )
    
    modify (\s -> s{objectsInfo = M.insert objName newRecord (objectsInfo s),
                    vTablesInfo = M.insert objName newVTEntry (vTablesInfo s)})

    where
    translateArg (Arg _ argT name) = (translateType argT, name)


checkObjectDefinition :: Object -> GeneratorM ()
checkObjectDefinition (ExtObjDef pos _ id ext (ClBlock _ decls)) = do
    buildVMT id (Just ext)
    objRecords <- gets objectsInfo
    let extRecord = objRecords ?! ext
        curRecord = objRecords ?! id
        adjRecord = curRecord{build_lastMO = build_lastMO extRecord,
                              build_lastVO = build_lastVO extRecord,
                              varOffsets = varOffsets extRecord,
                              objectSize = objectSize extRecord,
                              superClassOffsets = varOffsets extRecord,
                              superClassMethodTable =
                                M.union (methodTable extRecord)
                                        (superClassMethodTable extRecord),
                              superClass = Just ext}

    modify (\s -> s{objectsInfo = M.insert id adjRecord (objectsInfo s)})

    forM_ decls (buildObject id)
    objRecords <- gets objectsInfo

    let curRecord = objRecords ?! id
        finalMethodTable = M.union (methodTable curRecord) (superClassMethodTable curRecord)
        adjRecord = curRecord{methodTable = finalMethodTable}
    modify (\s ->s{objectsInfo = M.insert id adjRecord (objectsInfo s)})


checkObjectDefinition (ObjectDef pos _ id (ClBlock _ decls)) = do
    buildVMT id Nothing
    forM_ decls (buildObject id)



checkObjectDeclaration :: Object -> GeneratorM ()
checkObjectDeclaration obj = case obj of
    (ObjectDef pos _ id _) -> do
        checkExistance pos id

    (ExtObjDef pos _ id ext block) -> do
        checkExistance pos id


    where
        checkExistance pos id = do
            alreadyExists <- gets (isJust . M.lookup id . objectsInfo)
            when alreadyExists $
                makeCustomError "Name Error" pos "Klasa o podanej nazwie już istnieje.\n"

            -- Dodajemy pusty rekord
            modify (\s -> s {objectsInfo= M.insert id emptyRecord (objectsInfo s)})

addStandardLibrary :: GeneratorM ()
addStandardLibrary = do
    forM_ stdlib_h (\(fname, ftype, label) ->
        modify $ insertFunction fname ftype label
        )
    forM_ internallib_h (\(fname, ftype, label) ->
            modify $ insertFunction fname ftype label
        )
    where insertFunction fname ftype label s =
            s{funcLabels = M.insert (Ident fname) (ftype, label) (funcLabels s),
              functionsCode = M.insert (Ident fname)
                [Commented (FlowCtrlCode ReturnVoid) "internal builtin function"]
                (functionsCode s)}


staticStringsCode :: GeneratorState -> [String]
staticStringsCode state =
    let strings = M.assocs $ staticStrings state
    in
        map (\(str, lbl) -> lbl ++ ": db `" ++ (init . tail . show) str ++ "`, 0\n") strings


virtualTablesCode :: GeneratorState -> [String]
virtualTablesCode state =
    let emptySlot = "EMPTY_INSTRUCTION_SLOT"
        emptySlotDeclaration = emptySlot ++ " equ 0x0\n\n"
        blanksList = map ( , emptySlot) [0..]
        vTables = vTablesInfo state

        expandedVTables = M.map (\mapp ->
                let upperBound = safeMax mapp in
                    M.union mapp (M.fromList (take upperBound blanksList))
                ) vTables

        objsInfo = objectsInfo state
        labelInfoPairs = M.elems
                       $ M.mapWithKey (\k a ->
                            (virtualTableLabel $ objsInfo ?! k, M.assocs a))
                                                             expandedVTables

    in
        emptySlotDeclaration :
        map (\(lbl, mapp) -> let sorted = sortOn fst mapp in
                "align 16\n" ++
                lbl ++ ": \n" ++ unlines (map (("\tdq " ++) . (++ " - " ++ lbl)  . snd) mapp)) labelInfoPairs
    where
        safeMax m = if M.null m then 0
                    else fromInteger $ fst (M.findMax m)


prepareForCompilation :: Program -> GeneratorM ()
prepareForCompilation (Program _ definitions) = do

    addStandardLibrary

    -- Sprawdzamy poprawność deklaracji: unikalne nazwy, etc
    forM_ definitions checkDecl
    forM_ definitions checkObjDef

    -- Następnie generujemy kod dla każdej z funkcji
    forM_ definitions genCode

    where
        checkDecl (FnDef _ func) = void (checkFunctionDefinition func)
        checkDecl (ObDef _ obj)  = checkObjectDeclaration obj


        checkObjDef (FnDef _ _)  = return ()
        checkObjDef (ObDef _ obj) = checkObjectDefinition obj

        genCode (FnDef _ func)  = genFunction func
        genCode (ObDef _ obj)   = return ()






{-
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMWWWWMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMKkxOXMMMMMWXKWMMMMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMWkc:cdOKXXKOxOWMMMMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMNkl::lddxxxxk0XWMMMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMW0oloxxxooxxxkdx0NWMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMN0xxkkOOOo:cdkkdxKXWMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMNOxxkkOO00OOkOOd:ckXWMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMNOdxxxkkOOOOOkxxc..oKNMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMNOxxkkkxkkOOkkdolc;ckXWMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMW0kkkkkkkkkkkkkxxkkkO0NMMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMW0kkOOOOOOkkkkkkkkkkO0KNMMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMWN0kkkO0OOOOkkkkkkkkkkO0KKXNMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMWWWNNNXXNNNNXK0OkxdxkkO0OOOOOkkkkkkxkkO0OkxO0XNNNWWWWWWMMMMMMMMMMMM
MMMMMMMMMWNK00OOOkkkxxkkkxxxxxddxxkO0OOkkkkkkkkxxkO00OxxxxxxkkkkOOO000KXNWMMMMMM
MMMMMMMWX0kkkkkOOOOkkkxkkkkkkxxkkkkOOOOOOOOkkkkkkkOOOkxxxxxxxxxxkkkkkkkkkOXWMMMM
MMMMMWXOkkOkkOOOOOOOkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkOOOOkkkkkkKWMMM
MMMMWKkkOOOOOOOOOOkkkkkkOOOOkkkkkkkxxxxkkkxxkkkkkxxkkOOkkkkkkkkkkOOOOkOOOOOkKWMM
MMMMXOkOOOOOOOOOkkkkkkkkkkkkkkkkkxxxxxxxxxxxxxkxxkkkkkkkkkkkkkkxkOOOOOOOOOOOOXMM
MMMW0kOOOOOOOOOOOOkkkkkkkkkkkkkkkkkkkkxkkkxkxxxxxkkkkkkkkkkkkkkxkOOOOOOOOOOOkKWM
MMMXOkOOOOOOkkOkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkkxxxkkkkkkkkkkkkkkxxkOOOOOOOOOOk0WM
MMW0kOOOOOOOkOOkkxkkkkkkkkkkkkOkkkkkkkkOOkkOOkxxxkOkkkkkkkkkkkkxxkOkkOOOOOOOk0WM
MN0xkOOOOOOOkOOkkxxkkkkkkkkkkkkkkkkkkkkkOkkOOOkxxkkkkkkkkkkkkkkkxkOOkkOOOOOOkkXM
W0xxkkOOOOOOOOOkkxxxkkkkkkkkkkkOkkkOkkkkkkOOOOxdxkOOOOkkkkkkkkkxkkOOkOOOOOOOkx0W
NkxxkkkOOOOkkOkkxxxxxkkkkkkkkkkOOOOOOOOOOOOOkkxddxOOOOkkkkkkkxxkkkOOOOOOOOOkkxON
XkxxkkkkkkkkkkkkxxxkxxkkkkkkkOOOOOOOOOOOOOOOOkxddxOOOkkkkkkxxxxkkkOOkkOOOOkkxxON
NkxkkkOkkkkkkkkxxxxkkkxxxkkkkkOOOOOOOkOOOOOOOOxddxkkkkxkxxxddxxxxkkkkkkkOkkkxx0W
NOxkkkOkkkkxkkxxk0KOkkkxxxxxkkkOOOOOkkkkkkkkkkxdxxxxxxxxxxxxxxxxxkkkOkkkkkkkxkKM
NOxkkkkkkkkkkkxkKWMWXOkkxxxxxxxkkkxxxxxxxxxxxxxxxxxxkkkkkkkkO0OxxxkkkkkkkOOkxONM
XkkkkkkkkkkkkkkkOXWMWKkkkkkkkkkkkkxxxxxxxxxxxxxxkkkkOkkOOOkk0NNKOxxxxkkkkkkkk0WM
0kkkkkkkkkkkkkkkkkKWMWKkkkkkkkOOOkxxxxxxxxxkOOOxxkkkkkkk0OkOXWMN0kxkkkkkkkkkk0WM
OkkkkkkkkkkkkkkkkxkXMMWKkkkkkkkOOkxxxxxxxxxxkkkxxxkkOOkO00OKWMN0kkkkkkkkkkkkk0WM
Oxkkkkkkkkkkkkkkkxx0WMMN0xxxxxxkkxxxxxxkxxkkkOOxxkkkOOkO00OKWNOxkkkkkkkkkkkkk0WM
OxkkkkkOOkkkkkkkkxx0WMMWKkxxxxxkkkkkxxxxxxxxkOOxxkkOOOkO00kKN0xxkkkkkkkkkkkkk0WM
KkkOOOOkkkkkOOOkkxkXMMMMKkxxxxkkOOOOkxxxkkkkkOOxxkkkkkkkOkx0XOxxkkkkkkkkkkkkk0WM
W0kOOOOkkkOOOOOOkk0WMMMMXkxxxxxkOOOOOkxxxxkxkkOkxkOkkkkkxxkXWKxxkkkkkkkkkkkkkXMM
MWKOOOOOkkOOOOOOxkXMMMMMNOxxxxkkkkkOOOkxxxkxxkkkkkkkkOkxkONWMN0xxkOOOOkkkOOk0WMM
MMWXOOOOOkOOOOOkkxkKWMMMNOxxxkkkkkkkkOOkkkxxxkkxxkkkkkkxkKWMMWKkxkOOOOkkOOO0NMMM
MMMWXOOOOOOOOOOOOkxdkXWMXkxkkkkkkkkkkkkkkkxxOK0kkkOOkkkkx0WWXOxxkOOOOOOOOO0NMMMM
MMMMMWX00OOOOOOOOOkxddKWW0kkOkkkkkkkkkkkkkkKWMN0kOOOkkOkONNkddxkOOOOOO000KWMMMMM
MMMMMMWX00OOOOOOOOOkxdkNMNOkOOOOkkkOOOOkkOKWMMWKkkOOkOkkKWOodkOOOOOOOO00KWMMMMMM
MMMMMMMWNK0OO00000OxdoxXMMXOkOOOkkOOOOOKXNWMMMMNkkOOOkx0WW0dxxkO0000000KNMMMMMMM
MMMMMMMMMWX00000O0OkxkKWMMMKkkOOkkOOkOXWMMMMMMMWOxkOkkkXMWKxodk0000000KNMMMMMMMM
MMMMMMMMMMWNOO00kkO00XWMMMMWOxkkkkkk0NWMMMMMMMMNOxkkkxkXMMWN0kOOOO00OKWMMMMMMMMM
MMMMMMMMMMMMNNWNNXNWMMMMMMMWKkkkOkkkXMMMMMMMMMMXkkOkkkkXMMMMWXNXKXNWNWMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMN0OOOOOONMWMMMMMMMMXOOOOOOXWMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMXkkOOOKWMMMMMMMMMMXOOOkOXWMMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMW0kOOOXMMMMMMMMMMMN0kO0NMMMMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMW0kkOXWMMMMMMMMMMWKOOKXNWMMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMWXKKKXNMMMMMMMMMMMWWWNNWWMMMMMMMMMMMMMMMMMMMMMMMMM
MMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMMM
-}
