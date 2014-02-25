module Src.Prenex
 ( prenex
 ) where

import Src.AST
import Monads

{- Lleva una fórmula a su forma prenex -}
prenex  :: Form -> Form
prenex   = moveQuan . norm . moveNot . elimImp

{- 
   El primer paso para llevar una fórmula lógica a su forma
   normal prenex es eliminar las implicancias (y equivalencias).
-}
elimImp             :: Form -> Form
elimImp (Pred p ts)  = Pred p ts
elimImp (Not p)      = Not (elimImp p)
elimImp (And p q)    = And (elimImp p) (elimImp q)
elimImp (Or  p q)    = Or  (elimImp p) (elimImp q)
elimImp (Imp p q)    = Or (Not (elimImp p)) (elimImp q)
elimImp (Eq  p q)    = let p' = elimImp p
                           q' = elimImp q
                       in And (Or (Not p') q') (Or (Not q') p')
elimImp (Forall x f) = Forall x (elimImp f)
elimImp (Exists x f) = Exists x (elimImp f)
{- Luego de esta etapa ya no quedan "->" ni "==" -}

{-
   El segundo paso es desplazar las negaciones al interior de 
   la sentencia (por sobre las conjunciones, disyunciones y 
   cuantificadores).
-}
moveNot             :: Form -> Form
moveNot (Pred p ts)  = Pred p ts
moveNot (Not f)      = case f of
	Not p      -> moveNot p
	And p q    -> Or  (moveNot (Not p)) (moveNot (Not q))
	Or  p q    -> And (moveNot (Not p)) (moveNot (Not q))
	Forall x p -> Exists x (moveNot (Not p))
	Exists x p -> Forall x (moveNot (Not p))
	_          -> Not (moveNot f)
moveNot (And p q)    = And (moveNot p) (moveNot q)
moveNot (Or  p q)    = Or  (moveNot p) (moveNot q)
moveNot (Forall x f) = Forall x (moveNot f)
moveNot (Exists x f) = Exists x (moveNot f)
moveNot _            = error "Función moveNot: constructor inesperado"
{- Luego de esta etapa la negación queda delante de fórmulas atómicas -}

{-
   El siguiente paso es normalizar las variables para luego poder
   sacar los cuantificadores lo más afuera posible.
   En este paso no debería encontrarse nada que no sea disyunciones,
   conjunciones, cuantificadores y predicados.
-}
norm :: Form -> Form
norm f = fst $ runState (normAux f) (0, initEnv)

{-
   La función normAux toma una fórmula y devuelve una mónada que 
   contiene la fórmula equivalente con las variables normalizadas.
   Se utiliza la mónada State para llevar un estado con la cuenta de 
   las variables ya utilizadas y un entorno que será una función que
   transforma los nombres de las antiguas variables actualmente en 
   scope en los nuevos nombres de tales variables. La cuenta de las
   variables ya utilizadas se representa con un Int que se va 
   incrementando con cada nueva variable analizada. El entorno se
   representa con el tipo Env que es equivalente a una función de
   String a String.
-}
normAux             :: Form -> State (Int, Env) Form
normAux (Exists v f) = funAux1 Exists v f 
normAux (Forall v f) = funAux1 Forall v f
normAux (And p q)    = funAux2 And p q
normAux (Or  p q)    = funAux2 Or  p q
normAux (Pred p xs)  = do (_, e) <- get
                          return (Pred p (replace xs e))
normAux (Not f)      = do f' <- normAux f
                          return (Not f')
normAux _            = error "Función norm: constructor inesperado"


{- tipo que representa una función de transformación de variables -}
type Env = String -> String

{- entorno inicial, todas las variables están libres -}
initEnv  :: Env
initEnv v = error ("La variable " ++ v ++ " es libre")

{- función auxiliar para normalizar cuantificadores -}
funAux1       :: Quant -> String -> Form -> State (Int, Env) Form
funAux1 op v f = do (n, e) <- get
                    let v' = "x" ++ show (n+1)
                    let e' = (\s -> if s == v then v' else e s)
                    put (n+1, e')
                    f' <- normAux f
                    return (op v' f')

{- función auxiliar para normalizar operaciones binarias -}
funAux2       :: BinOp -> Form -> Form -> State (Int, Env) Form
funAux2 op p q = do (_, e) <- get
                    p' <- normAux p
                    (m, _) <- get
                    put (m, e)
                    q' <- normAux q
                    return (op p' q')

{- función que reemplaza todas las variables en la lista de términos
según la función de conversión -}               
replace :: [Term] -> Env -> [Term]
replace xs e = map (apply e) xs
    where
        apply e (Const c)   = Const c
        apply e (Func f ys) = Func f (replace ys e)
        apply e (Var v)     = Var (e v)

{-
   El siguiente paso es desplazar los cuantificadores hacia la 
   izquierda para que afecten a toda la fórmula y no sólo a 
   fórmulas parciales.
-}
moveQuan             :: Form -> Form
moveQuan (Pred p ts)  = Pred p ts
moveQuan (Not f)      = Not f
moveQuan (And p q)    = let p' = moveQuan p
                            q' = moveQuan q
                         in quanAux And p' q'
moveQuan (Or  p q)    = let p' = moveQuan p
                            q' = moveQuan q
                         in quanAux Or  p' q'
moveQuan (Forall x f) = Forall x (moveQuan f)
moveQuan (Exists x f) = Exists x (moveQuan f)
moveQuan _            = error "Función moveQuan: constructor inesperado"
{- Luego de esta etapa ya está en forma prenex -}

{- auxiliar para la función moveQuan -}
quanAux :: (Form -> Form -> Form) -> Form -> Form -> Form
quanAux op p q = case (p, q) of
	(Exists x r, Exists y s) -> Exists x (Exists y (quanAux op r s))
	(Exists x r, Forall y s) -> Exists x (quanAux op r (Forall y s))
	(Exists x r, _)          -> Exists x (quanAux op r q)
	(Forall x r, Exists y s) -> Exists y (quanAux op r (Forall x s))
	(Forall x r, Forall y s) -> Forall x (Forall y (quanAux op r s))
	(Forall x r, _)          -> Forall x (quanAux op r q)
	(_, Exists y s)          -> Exists y (quanAux op p s)
	(_, Forall y s)          -> Forall y (quanAux op p s)
	(_, _)                   -> op p q

