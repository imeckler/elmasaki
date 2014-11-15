module Sequence where

import QUtils

data Duration = Finite Time | Forever

type Seq a = (Duration, Time -> a)

forever : (Time -> a) -> Seq a
forever f = (Forever, f)

for : Time -> (Time -> a) -> Seq a
for dur f = (Finite dur, f)

stayFor : Time -> a -> Seq a
stayFor dur x = for dur (\_ -> x)

stayForever : a -> Seq a
stayForever x = forever (\_ -> x)

jumpTo : a -> Seq a
jumpTo x = stayFor 0 x

cycle : Seq a -> Seq a
cycle (dur, f) =
  case dur of
    Forever  -> (Forever, f)
    Finite d -> (Forever, \t -> f (QUtils.modFloat t d))

mkF d1 f1 f2 =
  \t -> if t <= d1 then f1 t else f2 (t - d1)

(>>>) : Seq a -> Seq a -> Seq a
(>>>) (dur1, f1) (dur2, f2) =
  case (dur1, dur2) of
    (Forever, _)           -> (Forever, f1)
    (Finite d1, Forever)   -> (Forever, mkF d1 f1 f2)
    (Finite d1, Finite d2) -> (Finite (d1 + d2), mkF d1 f1 f2)

concatSeq : [Seq a] -> Seq a
concatSeq = foldr1 (>>>)

runSeq : Seq a -> Time -> a
runSeq (_, f) = f

mapSeq : (a -> b) -> Seq a -> Seq b
mapSeq g (dur, f) = (dur, g << f)

