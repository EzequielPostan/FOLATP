module Monads where

--------------------------- Mónada Either -------------------------

instance Monad (Either e) where
--  return :: a -> Either e a
    return = Right
--  (>>=) :: Either e a -> (a -> Either e b) -> Either e b
    Left  l >>= _ = Left l
    Right r >>= k = k r

------------------------ Mónada Identidad --------------------------

newtype Identity a = Identity { runIdentity :: a }

instance Monad Identity where
--  return :: a -> Identity a
    return a = Identity a
--  (>>=) :: Identity a -> (a -> Identity b) -> Identity b
    Identity x >>= f = f x

--------------- Transformador de mónadas StateT ---------------------

newtype StateT s m a =
  StateT { runStateT :: (s -> m (a,s)) }

evalStateT :: Monad m => StateT s m a -> s -> m a
evalStateT m s = do (v,_) <- runStateT m s
                    return v

instance (Monad m) => Monad (StateT s m) where
--  return :: a -> StateT s m a
    return a = StateT $ \s -> return (a,s)
--  (>>=) :: StateT s m a -> (a -> StateT s m b) -> StateT s m b
    StateT h >>= f = StateT $ \s -> do (v,s') <- h s
                                       runStateT (f v) s'

get :: Monad m => StateT s m s
get   = StateT $ \s -> return (s,s)

put :: Monad m => s -> StateT s m ()
put s = StateT $ \_ -> return ((),s)

lift :: Monad m => m a -> StateT s m a
lift c = StateT $ \s -> do v <- c
                           return (v,s)


------------------------- Mónada State --------------------------------

type State s a = StateT s Identity a

runState :: State s a -> s -> (a,s)
runState m s = runIdentity (runStateT m s)

evalState :: State s a -> s -> a
evalState m s = fst (runState m s)

