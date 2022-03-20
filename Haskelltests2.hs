{-
pointers can only have information added. Read out of pointers is tracked.
writing a bigger value into pointers results in the value to create new subvariables. Problem: doubling values?
each pointer can have cached values on it like its propagators, its writing log etc.
Problem: That makes the theory a bit ugly...

Theory of pointer caching: Example: Scopes. Are just a state copied into itself. Normally one could not get the resulting pointer into the copy from the original pointer. Other example: Program traces. each part knows what caused it.

Values can only contain a constant or a tuple. A value containing the information of another value whether it is tuple or constant (or even which constant) is a sigma type. A pi type is the representation of a function.

Problem: Pointer creation kinda break lattice property

State Monad:
state : (S -> (S, A)) -> M A, where the given function needs to be a threshold function. It also needs to give the part of the state that was relevant. More precise:

state : Threshold S A -> M A
record ThresholdResult S A where
  nextState : S
  readState : S --smallest substate that still produces result
  result : A
record Threshold S A where
  func : S -> Maybe $ ThresholdResult S A
  func-prop : forall s res s'. (func s === just res) -> s leq s' -> func s' === just res
  thresh-prop : forall s res. (p : func s === just res) -> ThresholdResProp s func p
record ThresholdResProp (s : S) (func : S -> Maybe $ ThresholdResult S A) {res : ThresholdResult S A} (func s === just res) where
  readStateProp : func (readState res) === just res
  readStateMinProp : forall s'. s' < (readState res) -> func s' === nothing

example:
return x = state (Threshold {func = \s -> ThresholdResult {nextState = s; readState = top; result = x}; ... })

same works with pointers to DTC on functors f (Var a) !

state accumulates reasons that can be read out. Can be realised with all kinds of pointer types probably.
Problem: Transitive reasons. Need to be filtered out! When value is read, and reason for that value is subsumed by current reasons, that value is not added to reasons! This probably needs to be recursive...if any of its reasons is depending on the current reasons...and so on.



How does variable creation fit into this? Needs to be expressed as a threshold! THough is kinda like a return that just raises the state size. BUT! Variable itself has a reason for its creation!

ALSO: monad itself is a reason. If it weren't for the monad, none of the values would be written! Needs to be put down somewhere.


implication graph: Don't do reduction on write, that takes time. Do it when extracting the reason and remove all transitive implications.
-}

class VarMonad v m where
  new :: a -> m (v a)
  get :: v a -> m a
  modify :: v a -> (a -> (a,b)) -> m b
  put :: v a -> a -> m ()
  put p val = modify p (\_ -> (val, ()))


type (f :.: v) a = f (v a)

class DTCVarMonad v m where
  new :: m (v f) --here, there needs to be an implicit "top"
  get :: v f -> m (Fix (f :.: v)) --this waits until assignment
  put :: v f -> (Fix (f :.: v)) -> m () --here, lattice laws need to be obeyed

--to get unification running, following interface is needed (similar to unification-fd)
--can be created easily for DTC types
class ZipMatch f where
  getMatching :: f a -> f a -> Maybe [(a,a)]

class CLVarMonad v m where
  putReason :: v f -> [(v f, Fix (f :.: v))] -> m ()
  getReason :: v f -> m [[(v f, Fix (f :.: v))]] --reason would be some formula that if it holds, this thing gets its value
  getReason' :: v f -> m (m Bool) --what you'd actually be getting is a method that determines whether this pointer is ging to have its current value. This does not make a whole lot of sense when not parametrising this with the other pointers.

--reasons COULD get more complex by just being propagators, however that is not the information that can be extrated from the program. So we are going to stick with the given representation.
--reason needs to be recursively extracted. Could look like:

getMinReason :: v f -> m [(v f, Fix (f :.: v))]
getMinReason p = do {
  (safeHead -> res) <- getReason p
  smallRes <- filterM (\(r,_) -> getMinReason r >>= \mr -> return $ not $ mr `subseteq` ...) res
  {-
  Reasons always go from the first run of the program. Reason for every write is that entire history. We can only remove reasons where we read a value that we have previously written ourselves. Then we have this weird algorithm where "no reason" means it is just an initial axiom that needs to be kept, and if some values reasons are a subset of the reasons that we are already tracing it needs to be removed. If however a value has more reasons than traced (which can happen with parallelism), these new reasons need to be added, also discarding the value. So we recursively go deeper, stopping at writes that have no prior reason. Actually we are just generally recursively going down until all values have no more prior reasons.

  Length of reasons need to be cut. The longer a program runs, the more pior assumptions it has. Probably transitive thingys need to be filtered out somehow.
  -}
}

---------------------------------------------------------------
--dumb version
---------------------------------------------------------------

getOrigReason :: v f -> m [(v f, Fix (f :.: v))]
getOrigReason p = do
  res <- getReason p
  if (any isNull res)
  then return []
  else if isNull res
  then return [] --should never happen
  else concat <$> mapM getOrigReason (head res)

--------------------------------------------------------------
--VarMonads
--------------------------------------------------------------

data BaseVarMonad v m = BaseVarMonad {
  new :: a -> m (v a),
  get :: v a -> m a,
  modify :: v a -> (a -> (a, b)) -> m b,
}

put' :: BaseVarMonad v m -> v a -> (a -> a) -> m ()
put' (BaseVarMonad {...}) p f = modify p (\x -> (f x,()))

put :: BaseVarMonad v m -> v a -> a -> m ()
put (BaseVarMonad {...}) p a = put' p (const a)


--can detect reasons within variables
data ReasonVarMonad v m = ReasonVarMonad {
  new :: (HasTop a) => m (v a),
  split :: v a -> (a -> m b) -> m b,
  write :: v a -> a -> m ()
}
--this can be enhanced so that reasons work on every bind, where every intermediate value gets its own variable
data StrongReasonVarMonad v m = StrongReasonVarMonad {
  return :: Fix (f :.: v) -> m (v f),
  bind :: v f -> (Fix (f :.: v) ->  m (v g)) -> m (v g)
}
--watch out for polymorphism here

--TODO: there is no callback. Callback needs to be implemented into bind procedure.
data PropagationVarMonad v m = PropagationVarMonad {
  new :: a -> v a
  observe :: v a -> (a -> m ()) -> m ()
  write :: v a -> a -> m () --this might need some safety for things to only get assigned by lattice stuff
}

data MonadFork m = ForkMonad {
  fork :: m () -> m ()
}

baseToPropagation :: BaseVarMonad v m -> MonadFork m -> PropagationVarMonad v m
baseToPropagation vm@(BaseVarMonad new get modify) fm@(MonadFork fork) = PropagationVarMonad {
  new = \val -> new (val, []),
  observe = \p m -> put' vm (\(val, obs) -> (val, m : obs))
  modify = \p f -> modify vm (\(val, obs) -> let (val',res) <- f val in (sequence $ map fork obs) >> return ((val', obs), res))
}



baseToReason :: BaseVarMonad v m -> ReasonVarMonad v m
baseToReason (BaseVarMonad new get modify) = ReasonVarMonad {
  new = new top,
  split = --TODO: needs to be from propagation to Reason. Also...callback might not work nicely
}
