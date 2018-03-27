{-
 author: Luke Dercher
 student id: l446d901
 class: EECS 662

-}


{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad

-- BBAE AST and Type Definitions

liftNum :: (Int -> Int -> Int) -> BBAE -> BBAE -> BBAE
liftNum f (Num l) (Num r) = (Num (f l r))

liftBool :: (Bool -> Bool -> Bool) -> BBAE -> BBAE -> BBAE
liftBool f (Boolean l) (Boolean r) = (Boolean (f l r))

liftNum2Bool :: (Int -> Int -> Bool) -> BBAE -> BBAE -> BBAE
liftNum2Bool f (Num l) (Num r) = (Boolean (f l r))

data TBBAE where
  TNum :: TBBAE
  TBool :: TBBAE
  deriving (Show,Eq)

data BBAE where
  Num :: Int -> BBAE
  Plus :: BBAE -> BBAE -> BBAE
  Minus :: BBAE -> BBAE -> BBAE
  Bind :: String -> BBAE -> BBAE -> BBAE
  Id :: String -> BBAE
  Boolean :: Bool -> BBAE
  And :: BBAE -> BBAE -> BBAE
  Leq :: BBAE -> BBAE -> BBAE
  IsZero :: BBAE -> BBAE
  If :: BBAE -> BBAE -> BBAE -> BBAE
  deriving (Show,Eq)

type Env = [(String,BBAE)]

type Cont = [(String,TBBAE)]

subst :: String -> BBAE -> BBAE -> BBAE
subst _ _ (Num x) = (Num x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (Bind i' v' b') = if i==i'
	                        then (Bind i' (subst i v v') b')
	                        else (Bind i' (subst i v v') (subst i v b'))
subst i v (Id i') = if i==i'
	                then v
                  else (Id i')
subst _ _ (Boolean x) = (Boolean x)
subst i v (And l r) = (And (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero n) = (IsZero (subst i v n))
subst i v (If c t e) = (If (subst i v c)(subst i v t)(subst i v e))

 

evalS :: BBAE -> (Maybe BBAE)
evalS (Num x) = return (Num x)
evalS (Plus l r) = do { l' <- (evalS l) ;
                        r' <- (evalS r) ;
                        return (liftNum (+) l' r') }
evalS (Minus l r) = do { l' <- (evalS l) ;
                         r' <- (evalS r) ;
                         return (liftNum (-) l' r') }
evalS (Bind i v b) = do { v' <- (evalS v) ;
						             (evalS (subst i v' b)) }
evalS (Id id) = Nothing
evalS (Boolean x) = return (Boolean x)
evalS (And l r) = do { l' <- (evalS l);
                       r' <- (evalS r);
                       return (liftBool (&&) l' r')}
evalS (Leq l r) = do { l' <- (evalS l);
                       r' <- (evalS r);
                       return (liftNum2Bool (<=) l' r')}
evalS (IsZero n) = do { n' <- (evalS n);
                        return (liftNum2Bool (==) n' (Num 0)) }
evalS (If c t e) = do { (Boolean c') <- (evalS c);
                        if c' then (evalS t) else (evalS e)}

                        




evalM :: Env -> BBAE -> (Maybe BBAE)
evalM env (Num x) = (Just(Num x))
evalM env (Plus l r) = do { l' <- (evalM env l) ;
                            r' <- (evalM env r) ;
                            return (liftNum (+) l' r') }
evalM env (Minus l r) = do { l' <- (evalM env l) ;
                             r' <- (evalM env r) ;
                             return (liftNum (-) l' r') }
evalM env (Bind i v b) = do { v' <- (evalM env v) ;
						                  evalM ((i,v'):env) b }
evalM env (Id id) = lookup id env
evalM env (Boolean x) = (Just(Boolean x))
evalM env (And l r) = do { l' <- (evalM env l);
                           r' <- (evalM env r);
                           return (liftBool (&&) l' r')}
evalM env (Leq l r) = do { l' <- (evalM env l);
                           r' <- (evalM env r);
                           return (liftNum2Bool (<=) l' r')}
evalM env (IsZero n) = do { n' <- (evalM env n);
                            return (liftNum2Bool (==) n' (Num 0)) }
evalM env (If c t e) = do { (Boolean c') <- (evalM env c);
                            if c' then (evalM env t) else (evalM env e)}

testBBAE :: BBAE -> Bool
testBBAE (Num x) = if (evalS (Num x) == evalM [] (Num x)) then True else False
testBBAE (Plus l r) = if (evalS (Plus l r) == evalM [] (Plus l r)) then True else False
testBBAE (Minus l r) = if (evalS (Minus l r) == evalM [] (Minus l r)) then True else False
testBBAE (Bind i v b) = if (evalS (Bind i v b) == evalM [] (Bind i v b)) then True else False
testBBAE (Id id) = if (evalS (Id id) == evalM [] (Id id)) then True else False
testBBAE (Boolean x) = if (evalS (Boolean x) == evalM [] (Boolean x)) then True else False
testBBAE (And l r) = if (evalS (And l r) == evalM [] (And l r)) then True else False
testBBAE (Leq l r) = if (evalS (Leq l r) == evalM [] (Leq l r)) then True else False
testBBAE (IsZero n) = if (evalS (IsZero n) == evalM [] (IsZero n)) then True else False
testBBAE (If c t e) = if (evalS (If c t e) == evalM [] (If c t e)) then True else False


typeofM :: Cont -> BBAE -> (Maybe TBBAE)
typeofM con (Num _) = return TNum
typeofM con (Boolean _) = return TBool
typeofM con (Plus l r) = do l' <- (typeofM con l)
                            r' <- (typeofM con r)
                            if l' == TNum && r' == TNum
                            then  return TNum
                            else Nothing
typeofM con (Minus l r) = do l' <- (typeofM con l)
                             r' <- (typeofM con r)
                             if l' == TNum && r' == TNum
                             then return TNum
                             else Nothing
typeofM con (And l r) = do l' <- (typeofM con l)
                           r' <- (typeofM con r)
                           if l' == TBool && r' == TBool
                           then return TBool
                           else Nothing
typeofM con (Bind i v b) = do { v' <- (typeofM con v) ;
                              typeofM ((i,v'):con) b }
typeofM con (Id id) = lookup id con                            
typeofM con (Leq l r) = do l' <- (typeofM con l)
                           r' <- (typeofM con r)
                           if l' == TNum && r' == TNum
                           then return TBool
                           else Nothing
typeofM con (IsZero t) = do t' <- (typeofM con t)
                            if t' == TNum
                            then return TBool
                            else Nothing
typeofM con (If c t e) = do c' <- (typeofM con c)
                            t' <- (typeofM con t)
                            e' <- (typeofM con e)
                            if c' == TBool && t' == e'
                            then (return t')
                            else Nothing

evalT :: BBAE -> (Maybe BBAE)
evalT a = case (typeofM [] a) of
                (Just _) -> (evalM [] a)
                Nothing -> Nothing


