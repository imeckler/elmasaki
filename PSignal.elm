module PSignal where

import QUtils

data Duration = Finite Time | Forever

-- The P is for Pure and Partial.
type PSignal a = (Duration, Time -> a)

forever : (Time -> a) -> PSignal a
forever f = (Forever, f)

for : Time -> (Time -> a) -> PSignal a
for dur f = (Finite dur, f)

stayFor : Time -> a -> PSignal a
stayFor dur x = for dur (\_ -> x)

stayForever : a -> PSignal a
stayForever x = forever (\_ -> x)

jumpTo : a -> PSignal a
jumpTo x = stayFor 0 x

cycle : PSignal a -> PSignal a
cycle (dur, f) =
  case dur of
    Forever  -> (Forever, f)
    Finite d -> (Forever, \t -> f (QUtils.modFloat t d))

mkF d1 f1 f2 =
  \t -> if t <= d1 then f1 t else f2 (t - d1)

(>>>) : PSignal a -> PSignal a -> PSignal a
(>>>) (dur1, f1) (dur2, f2) =
  case (dur1, dur2) of
    (Forever, _)           -> (Forever, f1)
    (Finite d1, Forever)   -> (Forever, mkF d1 f1 f2)
    (Finite d1, Finite d2) -> (Finite (d1 + d2), mkF d1 f1 f2)

concatPSignal : [PSignal a] -> PSignal a
concatPSignal = foldr1 (>>>)

runPSignal : PSignal a -> Time -> a
runPSignal (_, f) = f

mapPSignal : (a -> b) -> PSignal a -> PSignal b
mapPSignal g (dur, f) = (dur, g << f)

