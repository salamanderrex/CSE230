-- ---
-- title: Homework #2, Due Friday 2/12/16
-- ---

{-# LANGUAGE TypeSynonymInstances #-}
module Hw2 where

import Control.Applicative hiding (empty, (<|>))
import Data.Map
import Control.Monad.State hiding (when)
import Text.Parsec hiding (State, between)
import Text.Parsec.Combinator hiding (between)
import Text.Parsec.Char
import Text.Parsec.String

-- Problem 0: All About You
-- ========================

-- Tell us your name, email and student ID, by replacing the respective
-- strings below

myName  = "Weiqi Zhang"
myEmail = "wez122@eng.ucsd.edu  "
mySID   = "A53093387"


-- Problem 1: All About `foldl`
-- ============================

-- Define the following functions by filling in the "error" portion:

-- 1. Describe `foldl` and give an implementation:

myFoldl :: (a -> b -> a) -> a -> [b] -> a
myFoldl f b []   = b
myFoldl f b (x:xs) = myFoldl f (f b x) xs


-- 2. Using the standard `foldl` (not `myFoldl`), define the list reverse function:

myReverse :: [a] -> [a]
myReverse xs = Prelude.foldl (\x l -> l:x) [] xs

-- 3. Define `foldr` in terms of `foldl`:

myFoldr :: (a -> b -> b) -> b -> [a] -> b
myFoldr f b xs = Prelude.foldl (\x1 x2 -> f x2 x1) b $ myReverse xs

-- 4. Define `foldl` in terms of the standard `foldr` (not `myFoldr`):

myFoldl2 :: (a -> b -> a) -> a -> [b] -> a
myFoldl2 f b xs = Prelude.foldr (\x1 x2 -> f x2 x1) b $ myReverse xs

-- 5. Try applying `foldl` to a gigantic list. Why is it so slow?
--    Try using `foldl'` (from [Data.List](http://www.haskell.org/ghc/docs/latest/html/libraries/base/Data-List.html#3))
--    instead; can you explain why it's faster?

--The reason that foldl is slow is because the recursion call of foldl will not be reduced untill foldl meets the last step '[]', and that will cause a long unreduced chain.
--After meet '[]', the reduction begins and will push N recursion calls on the stack to finish the recursion call, N is the size of the list that been applied with foldl.
--When N is large, the large amount of stack operations will be slow and might causes stack overflow.
--foldl's is implemented like:

--foldl' f z (x:xs) = let z' = z `f` x 
--                    in seq z' $ foldl' f z' xs

--For foldl', it leverage seq function to handle the problem that foldl meets. For seq a b, it will first evaluate a then b, if a is refered in b. 
--Then the long unreduced chain in foldl will not exist anymore: at each step in seq z' $ foldl' f z' xs, z' will evaluate first and then foldl' f z' xs.
--This avoids the operation consumption on stack, so will be faster.


-- Part 2: Binary Search Trees
-- ===========================

-- Recall the following type of binary search trees:

data BST k v = Emp
             | Bind k v (BST k v) (BST k v)
             deriving (Show)

-- Define a `delete` function for BSTs of this type:

delete :: (Ord k) => k -> BST k v -> BST k v
delete k Emp = Emp
delete k (Bind k' v t1 t2)
  |k == k' = helper t1 t2
  |k > k'  = Bind  k' v t1 $ Hw2.delete k t2
  |k < k'  = Bind  k' v (Hw2.delete k t1) t2

helper :: BST k v -> BST k v -> BST k v
helper Emp Emp                = Emp
helper Emp right              = right
helper left Emp               = left
helper left (Bind k v t1 t2)  = Bind k v (helper left t1) t2

-- Part 3: An Interpreter for WHILE
-- ================================

-- Next, you will use monads to build an evaluator for
-- a simple *WHILE* language. In this language, we will
-- represent different program variables as

type Variable = String

-- Programs in the language are simply values of the type

data Statement =
    Assign Variable Expression          -- x = e
  | If Expression Statement Statement   -- if (e) {s1} else {s2}
  | While Expression Statement          -- while (e) {s}
  | Sequence Statement Statement        -- s1; s2
  | Skip                                -- no-op
  deriving (Show)

-- where expressions are variables, constants or
-- binary operators applied to sub-expressions

data Expression =
    Var Variable                        -- x
  | Val Value                           -- v
  | Op  Bop Expression Expression
  deriving (Show)

-- and binary operators are simply two-ary functions

data Bop =
    Plus     -- (+)  :: Int  -> Int  -> Int
  | Minus    -- (-)  :: Int  -> Int  -> Int
  | Times    -- (*)  :: Int  -> Int  -> Int
  | Divide   -- (/)  :: Int  -> Int  -> Int
  | Gt       -- (>)  :: Int -> Int -> Bool
  | Ge       -- (>=) :: Int -> Int -> Bool
  | Lt       -- (<)  :: Int -> Int -> Bool
  | Le       -- (<=) :: Int -> Int -> Bool
  deriving (Show)

data Value =
    IntVal Int
  | BoolVal Bool
  deriving (Show)

-- We will represent the *store* i.e. the machine's memory, as an associative
-- map from `Variable` to `Value`

type Store = Map Variable Value

-- **Note:** we don't have exceptions (yet), so if a variable
-- is not found (eg because it is not initialized) simply return
-- the value `0`. In future assignments, we will add this as a
-- case where exceptions are thrown (the other case being type errors.)

-- We will use the standard library's `State`
-- [monad](http://hackage.haskell.org/packages/archive/mtl/latest/doc/html/Control-Monad-State-Lazy.html#g:2)
-- to represent the world-transformer.
-- Intuitively, `State s a` is equivalent to the world-transformer
-- `s -> (a, s)`. See the above documentation for more details.
-- You can ignore the bits about `StateT` for now.

-- Expression Evaluator
-- --------------------

-- First, write a function

evalE :: Expression -> State Store Value
evalE (Var x)      = do
                       s <- get
                       return (findWithDefault (IntVal 0) x s)

evalE (Val v)      = return v
evalE (Op o e1 e2) = do
                       (IntVal v1) <- evalE e1
                       (IntVal v2) <- evalE e2
                       return (evalOp o (IntVal v1) (IntVal v2))

-- that takes as input an expression and returns a world-transformer that
-- returns a value. Yes, right now, the transformer doesnt really transform
-- the world, but we will use the monad nevertheless as later, the world may
-- change, when we add exceptions and such.

-- **Hint:** The value `get` is of type `State Store Store`. Thus, to extract
-- the value of the "current store" in a variable `s` use `s <- get`.

evalOp :: Bop -> Value -> Value -> Value
evalOp Plus   (IntVal i) (IntVal j) = IntVal (i + j)
evalOp Minus  (IntVal i) (IntVal j) = IntVal (i - j)
evalOp Times  (IntVal i) (IntVal j) = IntVal (i * j)
evalOp Divide (IntVal i) (IntVal j) = IntVal (i `div` j)
evalOp Gt     (IntVal i) (IntVal j) = BoolVal (i > j)
evalOp Ge     (IntVal i) (IntVal j) = BoolVal (i >= j)
evalOp Lt     (IntVal i) (IntVal j) = BoolVal (i < j)
evalOp Le     (IntVal i) (IntVal j) = BoolVal (i <= j)
-- >






-- Statement Evaluator
-- -------------------

-- Next, write a function

evalS :: Statement -> State Store ()

-- that takes as input a statement and returns a world-transformer that
-- returns a unit. Here, the world-transformer should in fact update the input
-- store appropriately with the assignments executed in the course of
-- evaluating the `Statement`.

-- **Hint:** The value `put` is of type `Store -> State Store ()`.
-- Thus, to "update" the value of the store with the new store `s'`
-- do `put s'`.

evalS (Assign x e )    = do
                          s <- get
                          v <- evalE e
                          put $ insert x v s

evalS w@(While e s)    = do
                          v <- evalE e
                          case v of
                             IntVal  _     -> evalS Skip
                             BoolVal False -> evalS Skip
                             BoolVal True  -> do evalS s; evalS w
                             -- Do statement and check while again

evalS Skip             = return ()
evalS (Sequence s1 s2) = do
                           evalS s1
                           evalS s2
evalS (If e s1 s2)     =  do 
                           v <- evalE e
                           case v of
                             BoolVal True  -> evalS s1
                             BoolVal False -> evalS s2
                             IntVal  _     -> evalS Skip


-- In the `If` case, if `e` evaluates to a non-boolean value, just skip both
-- the branches. (We will convert it into a type error in the next homework.)
-- Finally, write a function

execS :: Statement -> Store -> Store
execS s = execState $ evalS s

-- such that `execS stmt store` returns the new `Store` that results
-- from evaluating the command `stmt` from the world `store`.
-- **Hint:** You may want to use the library function

-- ~~~~~{.haskell}
-- execState :: State s a -> s -> s
-- ~~~~~

-- When you are done with the above, the following function will
-- "run" a statement starting with the `empty` store (where no
-- variable is initialized). Running the program should print
-- the value of all variables at the end of execution.

run :: Statement -> IO ()
run stmt = do putStrLn "Output Store:"
              putStrLn $ show $ execS stmt empty

-- Here are a few "tests" that you can use to check your implementation.

w_test = (Sequence (Assign "X" (Op Plus (Op Minus (Op Plus (Val (IntVal 1)) (Val (IntVal 2))) (Val (IntVal 3))) (Op Plus (Val (IntVal 1)) (Val (IntVal 3))))) (Sequence (Assign "Y" (Val (IntVal 0))) (While (Op Gt (Var "X") (Val (IntVal 0))) (Sequence (Assign "Y" (Op Plus (Var "Y") (Var "X"))) (Assign "X" (Op Minus (Var "X") (Val (IntVal 1))))))))

w_fact = (Sequence (Assign "N" (Val (IntVal 2))) (Sequence (Assign "F" (Val (IntVal 1))) (While (Op Gt (Var "N") (Val (IntVal 0))) (Sequence (Assign "X" (Var "N")) (Sequence (Assign "Z" (Var "F")) (Sequence (While (Op Gt (Var "X") (Val (IntVal 1))) (Sequence (Assign "F" (Op Plus (Var "Z") (Var "F"))) (Assign "X" (Op Minus (Var "X") (Val (IntVal 1)))))) (Assign "N" (Op Minus (Var "N") (Val (IntVal 1))))))))))

-- As you can see, it is rather tedious to write the above tests! They
-- correspond to the code in the files `test.imp` and `fact.imp`. When you are
-- done, you should get

-- ~~~~~{.haskell}
-- ghci> run w_test
-- Output Store:
-- fromList [("X",IntVal 0),("Y",IntVal 10)]

-- ghci> run w_fact
-- Output Store:
-- fromList [("F",IntVal 2),("N",IntVal 0),("X",IntVal 1),("Z",IntVal 2)]
-- ~~~~~

-- Problem 4: A Parser for WHILE
-- =============================

-- It is rather tedious to have to specify individual programs as Haskell
-- values. For this problem, you will use parser combinators to build a parser
-- for the WHILE language from the previous problem.

-- Parsing Constants
-- -----------------

-- First, we will write parsers for the `Value` type

valueP :: Parser Value
valueP = intP <|> boolP

-- To do so, fill in the implementations of

intP :: Parser Value
intP = do
       x <- many1 digit
       return $ IntVal $ read x

-- Next, define a parser that will accept a
-- particular string `s` as a given value `x`

constP :: String -> a -> Parser a
constP s x = string s >> return x

-- and use the above to define a parser for boolean values
-- where `"true"` and `"false"` should be parsed appropriately.

boolP :: Parser Value
boolP = (constP "true" $ BoolVal True) <|> (constP "false" $ BoolVal False)

-- Continue to use the above to parse the binary operators

opP :: Parser Bop
opP =     constP "+"  Plus
      <|> constP "-"  Minus
      <|> constP "*"  Times
      <|> constP "/"  Divide
      <|> constP ">"  Gt
      <|> constP ">=" Ge
      <|> constP "<"  Lt
      <|> constP "<=" Le


-- Parsing Expressions
-- -------------------

-- Next, the following is a parser for variables, where each
-- variable is one-or-more uppercase letters.

varP :: Parser Variable
varP = many1 upper

-- Use the above to write a parser f-or `Expression` values

variableExpr :: Parser Expression
variableExpr = do v <- varP
                  return $ Var v

valExpr :: Parser Expression
valExpr = do v <- valueP
             return $ Val v

parenExpr :: Parser Expression
parenExpr = do string "("
               e <- exprP
               string ")"
               return e

baseExpr :: Parser Expression
baseExpr = variableExpr <|> valExpr <|> parenExpr

exprOp :: Expression -> Parser Expression
exprOp e1 = do op <- opP
               spaces
               e2 <- exprP
               return $ Op op e1 e2

exprP :: Parser Expression
exprP = do e <- baseExpr
           spaces
           exprOp e <|> return e

-- Parsing Statements
-- ------------------

-- Next, use the expression parsers to build a statement parser

assignStmt :: Parser Statement
assignStmt = do v <- varP
                spaces; string ":="; spaces
                e <- exprP
                return $ Assign v e

ifStmt :: Parser Statement
ifStmt = do string "if"; spaces
            e <- exprP
            spaces; string "then"; spaces
            s1 <- statementP
            spaces; string "else"; spaces
            s2 <- statementP
            spaces; string "endif"
            return $ If e s1 s2

whileStmt :: Parser Statement
whileStmt = do string "while"; spaces
               e <- exprP
               spaces; string "do"; spaces
               s <- statementP
               spaces; string "endwhile"
               return $ While e s

skipStmt :: Parser Statement
skipStmt = string "skip" >> return Skip

baseStmt :: Parser Statement
baseStmt = assignStmt <|> ifStmt <|> whileStmt <|> skipStmt

seqStatement :: Statement -> Parser Statement
seqStatement s1 = do char ';'; spaces
                     s2 <- statementP
                     return $ Sequence s1 s2


statementP :: Parser Statement
statementP = do s <- baseStmt
                seqStatement s <|> return s

-- When you are done, we can put the parser and evaluator together
-- in the end-to-end interpreter function

runFile s = do p <- parseFromFile statementP s
               case p of
                 Left err   -> print err
                 Right stmt -> run stmt

-- When you are done you should see the following at the ghci prompt

-- ~~~~~{.haskell}
-- ghci> runFile "test.imp"
-- Output Store:
-- fromList [("X",IntVal 0),("Y",IntVal 10)]

-- ghci> runFile "fact.imp"
-- Output Store:
-- fromList [("F",IntVal 2),("N",IntVal 0),("X",IntVal 1),("Z",IntVal 2)]
-- ~~~~~





