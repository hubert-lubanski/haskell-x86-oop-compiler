module Types where
import Common
import Grammar.Abs
import qualified Grammar.Abs as ABS
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.Identity (Identity)
import Control.Monad.State (StateT)
import Control.Monad.Reader (ReaderT)
import Control.Monad.Except (ExceptT)
import Prelude
import Error
import Common (appendAt)
import GHC.Stack (HasCallStack)


(?!) ::  (HasCallStack, Show k, Ord k) => M.Map k a -> k -> a
(?!) map key  = M.findWithDefault mapError key map
    where
        mapError = error ("Key (" ++ show key ++ ") not in map ")



getS :: Ident -> String
getS (Ident s) = s

type VarName    = Ident
type FunName    = Ident
type ObjName    = Ident
type ClassName  = Ident


{-------------------------------------------------------------------------------
                    Generator Kodu Czwórkowego
-------------------------------------------------------------------------------}

type Label      = String
type Location   = Integer

-- Value loc => Zmienna na pozycji 'loc' przechowuje wartość
-- Reference loc => zmienna na pozycji 'loc' przechowuje adres
data Value      = Value Location | Reference Location
    deriving (Eq, Ord)
instance Show Value where
    show (Value loc) = show loc
    show (Reference loc) = show loc ++ "&"
data Variable   = Local Value | Parameter Value | Dereferenced Variable
    deriving (Eq, Ord)
instance Show Variable where
    show (Local val) = "l" ++ show val
    show (Parameter val) = "p" ++ show val
    show (Dereferenced var) = show var ++ "d"

data Operand        = Variable Variable
                    | Immediate Int
                    | Undefined String
    deriving (Eq, Ord)

isVariable :: Operand -> Bool
isVariable (Variable _) = True
isVariable _ = False

isDereference :: Operand -> Bool
isDereference (Variable (Dereferenced _)) = True
isDereference _ = False

isImmediate :: Operand -> Bool
isImmediate (Immediate _) = True
isImmediate _ = False

instance Show Operand where
    show (Variable v) = show v
    show (Immediate i) = "imm" ++ show i
    show (Undefined str) = magentaColor str


data BinOp          = Add | Sub | Mul | Div | Mod
    deriving (Eq, Show)
data CondOp         = LT  | LE  | GT  | GE  | EQ  | NE | AND | OR
    deriving (Eq)

negateCondOp :: CondOp -> CondOp
negateCondOp Types.LT = Types.GE
negateCondOp Types.LE = Types.GT
negateCondOp Types.GT = Types.LE
negateCondOp Types.GE = Types.LT
negateCondOp Types.EQ = Types.NE
negateCondOp AND      = AND
negateCondOp OR       = OR

instance Show CondOp where
    show Types.LT = "<"
    show Types.LE = "<="
    show Types.GT = ">"
    show Types.GE = ">="
    show Types.EQ = "=="
    show Types.NE = "!="
    show AND = blueColor "and"
    show OR  = blueColor "or"

translateRelOp :: RelOp -> CondOp
translateRelOp (ABS.LTH _)  = Types.LT
translateRelOp (ABS.LE _)   = Types.LE
translateRelOp (ABS.GTH _)  = Types.GT
translateRelOp (ABS.GE _)   = Types.GE
translateRelOp (ABS.EQU _)  = Types.EQ
translateRelOp (ABS.NE _)   = Types.NE

data UnrOp          = Not | Neg
    deriving (Eq, Show)

data ValueOper      = Binary Operand BinOp Operand
                    | Unary UnrOp Operand
                    -- Address calculation --
                    | LoadAddressFull Operand Operand Integer Integer   -- &a[i*size + 42]
                    | LoadAddressArray Operand Operand Integer          -- &a[i*size]
                    | LoadAddressOffset Operand Integer                 -- &a[42]
                    | LoadAddressLabel Label
                    -- Dereferencing --
                    | LoadFrom Operand                      -- reg1 := *reg2 | *imm
                    -- Assignment --
                    | CopyOf Operand                    -- reg1 := reg2 | imm
                    -- Function calls --
                    | Call Label [Operand]
                    | CallReg Operand [Operand]
    deriving (Eq)
instance Show ValueOper where
    show (Binary a1 oper a2) = show oper ++ " " ++ show a1 ++ ", " ++ show a2
    show (Unary uop a)       = show uop ++ " " ++ show a
    -- show (Condition a1 cond a2) = "(" ++ show a1 ++ " " ++ show cond ++ " " ++ show a2 ++ " ? " ++ blueColor "true" ++ " : " ++ blueColor "false" ++ ")"
    show (LoadAddressFull a i s o) = concat ["lea [", show a, " + ", show i, "*", show s, " + ", show o, "]"]
    show (LoadAddressArray a i s) = concat ["lea [", show a, " + ", show i, "*", show s, "]"]
    show (LoadAddressOffset a o) = concat ["lea [", show a, " + ", show o, "]"]
    show (LoadAddressLabel l) = concat ["lea [", altblueColor "rel ", l, "]"]
    show (LoadFrom a1)       = "[" ++ show a1 ++ "]"
    show (CopyOf a1)         = show a1
    show (Call l ops)        = altmagentaColor "call " ++ l ++ " " ++ show ops
    show (CallReg a1 args)   = altmagentaColor "call " ++ "[" ++ show a1 ++ "] " ++ show args

data FlowCtrlOper   = Jump Label
                    | ConditionalFull Operand CondOp Operand Label Label
                    | InsertLabel Label
                    | Return Operand
                    | ReturnVoid
    deriving (Eq)
instance Show FlowCtrlOper where
    show (Jump l) = altmagentaColor "Jump " ++ l
    show (ConditionalFull a1 c a2 l1 l2) = altmagentaColor "if " ++ show a1 ++ " " ++ show c ++ " " ++ show a2 ++ altmagentaColor " then " ++ l1 ++ " else " ++ l2
    show (InsertLabel l) = yellowColor l
    show (Return o) = altmagentaColor "Return " ++ show o
    show ReturnVoid = altmagentaColor "Return "


data QuadCode       = ValueCode  Operand ValueOper      -- Register  := value
                    | ReferenceCode Operand ValueOper   -- *Register := value
                    | FlowCtrlCode FlowCtrlOper
                    | Commented QuadCode String
                    | PhiFunction Operand [(Label, Operand)]
    deriving (Eq)
instance Show QuadCode where
    show (ValueCode op vop) = appendAt 5 (show op) " := " ++ show vop
    show (ReferenceCode op vop) = appendAt 5 ("["++show op++"]") " := " ++ show vop
    show (FlowCtrlCode flow) = show flow
    show (Commented code comment) = appendAt 40 (show code) (greenColor ("; " ++ comment))
    show (PhiFunction op values) = appendAt 5 (show op) " <- "++ greenColor "phi(" ++ concatMap (\(l,v) -> yellowColor l ++ " " ++ show v ++ "; ") values ++ greenColor ")"

infixl 1 #=
(#=) :: Operand -> ValueOper -> QuadCode
(#=) = ValueCode

(-:) :: FlowCtrlOper -> QuadCode
(-:) = FlowCtrlCode

infixl 1 @=
(@=) :: Operand -> ValueOper -> QuadCode
(@=) = ReferenceCode

infixr 0 //
(//) :: QuadCode -> String -> QuadCode
(//) = Commented

{-------------------------------------------------------------------------------
                    Sprawdzanie Typów
-------------------------------------------------------------------------------}


data VarType    = Int    | Boolean      | Void          |
                  String | Custom Ident | Array VarType
    deriving (Eq, Show)

translateBasicType :: BasicType -> VarType
translateBasicType basic = case basic of
    TBuiltin _ builtin  -> case builtin of
        TInt _  -> Int
        TStr _  -> String
        TBool _ -> Boolean
        TVoid _ -> Void
    TObject _ name      -> Custom name

translateType :: Type -> VarType
translateType (TBasic _ basic) = translateBasicType basic
translateType (TArray _ (AType _ atype)) = Array (translateType atype)



data FunType    = Func {retType:: VarType, argTypes:: [VarType]}
    deriving (Show)

type Result         = (VarType, Operand)
type Callable       = (FunType, Label)


invertible :: VarType -> Bool
invertible Int  = True
invertible _    = False

negatable :: VarType -> Bool
negatable Boolean   = True
negatable _         = False

comparable :: VarType -> Bool
comparable Int      = True
comparable Boolean  = True
comparable _        = False

compound :: VarType -> Bool
compound (Array _)  = True
compound (Custom _) = True
compound _          = False

castableTo :: VarType -> VarType -> Bool
castableTo Void (Custom _) = True
castableTo _ _ = False

isReference :: VarType -> Bool
isReference (Array _) = True
isReference (Custom _)= True
isReference String = True
isReference _ = False

equivalenceCapable :: VarType -> VarType -> Bool
equivalenceCapable String _ = False
equivalenceCapable _ String = False
-- equivalenceCapable (Custom _) Void = True
-- equivalenceCapable Void (Custom _) = True
equivalenceCapable x y = x == y






{-------------------------------------------------------------------------------
                    Struktury
-------------------------------------------------------------------------------}

-- Opis informacji o strukturach danego typu --
{--
Obiekt: [---------------]
        Virtual Table Address   0
        Zmienne A1,              8
        Zmienne A2,              8 + sizeof(A)
        ...
        Zmienne AN               8 + sum_i (sizeof(Ai))
        [---------------]
Wywołanie metody:
Metoda <--> numer w tablicy
    - Załaduj VTA do R
    - Załaduj [R + sizeof(ptr) * numer_metody] do R
--}
objectVTAOffset = -8
arrayLengthOffset = -8
{--
Tablica:[---------------]
        length              (offset: -1)
        data [0...length-1]
        [---------------]
--}
data ObjectRecord = ObjectRecord {
    objectSize        :: Integer,             -- Wielkość w bajtach obiektu
    virtualTableLabel :: Label,

    superClass        :: Maybe ClassName,
    superClassOffsets :: Map VarName (VarType, Integer), -- Offset pól nadklasy
    varOffsets        :: Map VarName (VarType, Integer), -- Offset pól tej klasy
    build_lastVO      :: Integer,
    
    superClassMethodTable :: Map FunName (FunName, Integer),
    methodTable       :: Map FunName (FunName, Integer),-- Indeksy metod obiektu
    build_lastMO      :: Integer
}

emptyRecord = ObjectRecord {
    objectSize = 0,
    virtualTableLabel = "",

    superClass = Nothing,
    superClassOffsets = M.empty,
    varOffsets = M.empty,
    build_lastVO = 0,

    superClassMethodTable = M.empty,
    methodTable = M.empty,
    build_lastMO = 0
}

data GeneratorState = GeneratorState {
    -- Static --
    regCounter    :: Integer,
    generatedCode :: [QuadCode],

    hasReturn     :: Bool,
    lastInstr     :: Position,

    -- Globals --
    labelSuffix     :: Integer,
    loopLabelSuffix :: Integer,
    condLabelSuffix :: Integer,
    stringLabelSuffix :: Integer,

    funcLabels    :: Map FunName Callable,
    functionsCode :: Map FunName [QuadCode],
    vTablesInfo   :: Map ClassName (Map Integer Label),

    objectsInfo   :: Map ClassName ObjectRecord,
    maxRegCounter :: Integer,

    staticStrings :: Map String Label
}

gState :: GeneratorState
gState = GeneratorState {
            regCounter = 0,
            generatedCode = [],
            hasReturn = False,
            lastInstr = Just (0,0),
            labelSuffix = 0,
            loopLabelSuffix = 0,
            condLabelSuffix = 0,
            stringLabelSuffix = 0,
            
            funcLabels = M.empty,
            functionsCode = M.empty,

            vTablesInfo = M.empty,

            objectsInfo = M.empty,
            maxRegCounter = 0,

            staticStrings = M.empty
        }

data Scope = FunctionScope FunName | MethodScope ClassName Operand FunName

data GeneratorEnv   = GEnv {
    -- Locals (inside function or block of code) --
    lastVarBindOP   :: Map VarName Result,
    varOpBind       :: Map VarName Result,
    currentScope    :: Scope
}



gEnv = GEnv  {
            lastVarBindOP = M.empty,
            varOpBind = M.empty,
            currentScope = FunctionScope (Ident "")
        }

type GeneratorM a   = ExceptT Err (StateT GeneratorState (ReaderT GeneratorEnv IO)) a
