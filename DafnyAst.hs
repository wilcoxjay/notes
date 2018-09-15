{-# LANGUAGE ScopedTypeVariables #-}

import Data.List as List
import Test.QuickCheck
import System.Process
import System.IO

data Type = TyBool | TyInt | TySeq Type
  deriving (Eq, Show)

data Quant = Forall | Exists
  deriving Show

data BinOp = Plus | And | Or | Lt | Implies | Eq
  deriving Show

newtype Ident = Ident String
  deriving (Eq, Show)

type BVars = [(Ident, Type)]

data Expr =
    EVar Ident
  | EIntLit Int
  | EBoolLit Bool
  | ESeqLit [Expr]
  | EQuant Quant BVars Expr
  | EBinOp BinOp Expr Expr
  | EIndex Expr Expr
  deriving Show

data Decl =
  Function Ident BVars Type Expr
  deriving Show

showType TyBool = "bool"
showType TyInt = "int"
showType (TySeq ty) = "seq<" ++ showType ty ++ ">"

showBVar (Ident v, ty) = v ++ ": " ++ showType ty

showBVars :: BVars -> String
showBVars bvs = intercalate ", " (map showBVar bvs)

data Prec =
    PrecAtom
  | PrecPlus
  | PrecCmp
  | PrecAnd
  | PrecOr
  | PrecImplies
  | PrecQuant
  | PrecTop

precLevel PrecAtom    = 1
precLevel PrecPlus    = 2
precLevel PrecCmp     = 3
precLevel PrecAnd     = 4
precLevel PrecOr      = 5
precLevel PrecImplies = 6
precLevel PrecQuant   = 7
precLevel PrecTop     = 10

opPrec Plus    = PrecPlus
opPrec And     = PrecAnd
opPrec Or      = PrecOr
opPrec Implies = PrecImplies
opPrec Lt      = PrecCmp
opPrec Eq      = PrecCmp

data Assoc = AssocLeft | AssocRight | AssocNone
  deriving Eq
precAssoc PrecAtom    = AssocNone
precAssoc PrecPlus    = AssocLeft
precAssoc PrecCmp     = AssocNone
precAssoc PrecAnd     = AssocLeft
precAssoc PrecOr      = AssocLeft
precAssoc PrecImplies = AssocRight
precAssoc PrecQuant   = AssocNone
precAssoc PrecTop     = AssocNone

noParens child parent side =
  precLevel child < precLevel parent ||
  (precLevel child == precLevel parent && precAssoc child == side)
  
exprPrec (EVar _) = PrecAtom
exprPrec (EIntLit _) = PrecAtom
exprPrec (EBoolLit _) = PrecAtom
exprPrec (ESeqLit _) = PrecAtom
exprPrec (EQuant _ _ _) = PrecQuant
exprPrec (EBinOp op _ _) = opPrec op
exprPrec (EIndex _ _) = PrecAtom

showQuant Forall = "forall"
showQuant Exists = "exists"

instance Arbitrary Quant where
  arbitrary =
    -- elements [Forall, Exists]
    return Forall

showOp Plus    = "+"
showOp And     = "&&"
showOp Or      = "||"
showOp Implies = "==>"
showOp Lt      = "<"
showOp Eq      = "=="

showExpr :: Expr -> String
showExpr e = showExpr' PrecTop AssocNone e 
  where showExpr' prec assoc e =
          if not (noParens (exprPrec e) prec assoc)
          then "(" ++ showExpr' PrecTop AssocNone e ++ ")"
          else go e
          where
            go (EVar (Ident x)) = x
            go (EIntLit n) = show n
            go (EBoolLit b) = show b
            go (ESeqLit l) = "[" ++ intercalate ", " (map showExpr l) ++ "]"
            go (EQuant q bvs body) = showQuant q ++ " " ++ showBVars bvs ++ " :: " ++
                                     showExpr' PrecQuant AssocNone body
            go (EBinOp op e1 e2) = showExpr' (exprPrec e) AssocLeft e1 ++
                                   " " ++ showOp op ++ " " ++
                                   showExpr' (exprPrec e) AssocRight e2
            go (EIndex e1 e2) = showExpr' PrecAtom AssocNone e1 ++ "[" ++
                                showExpr' PrecAtom AssocNone e2 ++ "]"

showDecl (Function (Ident nm) bvs retty body) =
  "function " ++ nm ++ "(" ++ showBVars bvs ++ "): " ++ showType retty ++ " { " ++
    showExpr body ++
  " }"

f = Function (Ident "F")
       [(Ident "l", TySeq TyBool), (Ident "x", TyBool), (Ident "is", TySeq TyInt)] TyBool
       (EQuant Forall [(Ident "i", TyInt), (Ident "j", TyInt)]
         (EBinOp Implies
           (EBinOp And (EBinOp Lt (EIndex (EVar (Ident "is")) (EVar (Ident "i")))
                                  (EVar (Ident "j")))
                       (EBinOp Lt (EVar (Ident "j"))
                                  (EIndex (EVar (Ident "is"))
                                          (EBinOp Plus (EVar (Ident "i")) (EIntLit 1)))))
           (EBinOp Eq (EIndex (EVar (Ident "l")) (EVar (Ident "j"))) (EVar (Ident "x")))))

genType :: Gen Type
genType = sized genType'
  where genType' 0 = elements [TyInt, TyBool]
        genType' n = frequency [ (1, return TyInt)
                               , (3, return TyBool)
                               , (1, TySeq <$> genType' (n - 1))
                               ]

instance Arbitrary Type where
  arbitrary = genType

instance Arbitrary Ident where
  arbitrary = do c <- elements "abcdefghijklmnopqrstuvwxyz"
                 return (Ident [c])
  

genVar :: [(Ident, Type)] -> Type -> [Gen Expr]
genVar ctx ty =
  let l = filter (\(_, xty) -> xty == ty) ctx
  in (if null l then [] else [do (x, _) <- elements l; return (EVar x)])

genExpr ctx ty = sized (genExpr' ctx ty)
  where genExpr' ctx ty 0 = smallExpr ctx ty
        genExpr' ctx ty n = oneof [ smallExpr ctx ty
                                  , recExpr ctx ty
                                  ]
          where 
            recExpr ctx ty = frequency [ (3, recExpr' ctx ty)
                                       , (1, EIndex <$> subExpr ctx (TySeq ty) <*> subExpr ctx TyInt)
                                       ]

            recExpr' ctx ty = case ty of
              TyInt -> EBinOp Plus <$> smallExpr ctx ty <*> smallExpr ctx ty
              TyBool -> frequency [ (2, EBinOp And <$> subExpr ctx ty <*> subExpr ctx ty)
--                                  , (2, EBinOp Or <$> subExpr ctx ty <*> subExpr ctx ty)
                                  , (2, EBinOp Implies <$> subExpr ctx ty <*> subExpr ctx ty)
                                  , (1, EBinOp Lt <$> subExpr ctx TyInt <*> subExpr ctx TyInt)
                                  , (1, do ty' <- resize (n - 1) arbitrary
                                           EBinOp Eq <$> subExpr ctx ty' <*> subExpr ctx ty')
                                  , (2, do bvs <- resize (min 3 (n - 1)) (listOf1 arbitrary)
                                           EQuant <$> arbitrary <*> return bvs <*>
                                             subExpr (bvs ++ ctx) ty)
                                  ]

              TySeq ty' -> ESeqLit <$> resize (n - 1) (listOf (genExpr' ctx ty' (n - 1)))
              
            subExpr ctx ty = genExpr' ctx ty (n - 1)
  
        smallExpr ctx ty =
          oneof (genVar ctx ty ++
                  [case ty of
                      TyInt -> EIntLit <$> arbitrary
                      TyBool -> EBoolLit <$> arbitrary
                      TySeq _ -> return (ESeqLit [])])

instance Arbitrary Decl where
  arbitrary = do f <- arbitrary
                 -- args <- resize 5 arbitrary
                 -- retty <- arbitrary
                 -- Function f args retty <$> genExpr args retty
                 let args = [(Ident "l", TySeq TyBool), (Ident "x", TyBool), (Ident "is", TySeq TyInt)] 
                     retty = TyBool in
                   Function f args retty <$> genExpr args retty

theFile :: FilePath
theFile = "/Users/jrw/build/notes/tmp.dfy"

crashes :: String -> IO Bool
crashes s = do
  writeFile theFile s
  (_, _, Just h, _) <- createProcess (proc "dafny" [theFile]) { std_out = NoStream,
                                                                std_err = CreatePipe }
  s <- hGetContents h
  return $ "[ERROR] FATAL UNHANDLED EXCEPTION" `isInfixOf` s
  
findCrash :: IO ()
findCrash = (putStrLn "" >> go 0)
  where go n =
          do putStr ("\r" ++ show n)
             hFlush stdout
             s <- showDecl <$> generate (resize 10 arbitrary)
             b <- crashes s
             if b then return ()
             else go (n + 1)

main :: IO ()
main =
  findCrash
--  do d :: Decl <- generate (resize 10 arbitrary)
--     putStrLn (showDecl d)
        
  
