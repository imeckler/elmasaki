module Queue where

-- This module implements functional Queues as described in Okasaki 1996
-- (http://www.cs.cmu.edu/~rwh/theses/okasaki.pdf) along with types
-- reifying operations on those queues.

import Sequence (..)
import Regex (..)
import Maybe
import String (toInt)

-- In our quest to achieve good performance, we represent queues as a pair
-- of lists: the first representing the front of the queue, and the second
-- representing the back (in reverse order). The point is that it's easy to
-- perform both of the essential queue operations.
-- 1. Popping an element off the front of the queue (assuming it's non-empty)
--    is as easy as taking the head of the first list in the pair.
-- 2. Pushing an element onto the back of the queue is just consing onto the
--    second list in the pair, since we're representing the back of the queue
--    in reverse.
type Queue a = ([a], [a])

put : a -> Queue a -> Queue a
put x (xs, ys) = (xs, x::ys)

pop : Queue a -> Maybe (a, Queue a)
pop q = 
  case q of
    ([], [])    -> Nothing
    ([], ys)    -> pop (reverse ys, [])
    (x::xs, ys) -> Just (x, (xs, ys))

-- If the front view of the queue is empty when we try to pop, we reverse the back
-- and try to pop from there. Reversing takes time O(n) where n is the length of
-- the back view, but we won't have to do it again for another n steps, so it has
-- an amortized cost of O(1).

-- Now let's make an animation of such a queue. Recall the notion of a `Signal`.
-- Conceptually, a `Signal a` can be thought of as function `Time -> a`. For example,
-- the user's mouse position can be represented as a pair `(Int, Int)` which is a function
-- of `Time`, and indeed there is a value in elm `Mouse.position : Signal (Int, Int)`.
-- As another example, the type of graphics in Elm is called `Form`, so an animation would
-- have type `Signal Form`.

-- Back to animating queues. First we must have a little dialogue with ourselves:
-- Q: What is it that we want to animate?
-- A: We want to animate the push and pop commands being performed on the above queue data.
-- Q: Where will the commands for the queue come from?
-- A: They will come from the user.
-- Q: How do we represent this input from the user.
-- A: We make a type reifying the possible commands the user can make

data QueueCommand a
  = Put a
  | Pop

-- and then we build a signal of type `Signal (QueueCommand a)`, which represents the stream
-- of queue commands. This signal is actually defined in the Main module, so we'll shelve
-- discussion of getting the input for later. For now, let's just suppose we have such a signal.

-- The `QueueCommand`s themselves aren't directly animatable. The `Pop` command in particular
-- could have many different animations associated to it depending on the state of the queue:
-- Sometimes it just pops an element off the left list, sometimes it causes the right list
-- to be reversed and shuffled over to the left list. These two things should of course be
-- animated differently.

-- So, with that in mind, we define the following type, which more directly represents the
-- exact operations being performed on a queue.

data QueueOp a
  = PutRight a
  | PopLeft a
  | RightToLeft a
  | EmptyError
  | Nop

-- The idea now will be to somehow interpret our `Signal (QueueCommand a)` into
-- a `Signal (QueueOp a, Queue a)` (or something along those lines)
-- which can be more easily animated.

rightToLeft : Queue a -> [(QueueOp a, Queue a)]
rightToLeft q =
  case q of
    (xs, [])    -> execPop (xs, [])
    (xs, y::ys) -> let q' = (y::xs,ys) in (RightToLeft y, q') :: rightToLeft q'

execPop : Queue a -> [(QueueOp a, Queue a)]
execPop q =
  case q of
    ([], [])    -> [(EmptyError, q)]
    (x::xs, ys) -> [(PopLeft x, (xs, ys))]
    _           -> rightToLeft q

execPut : a -> Queue a -> [(QueueOp a, Queue a)]
execPut x (xs, ys) = [(PutRight x, (xs, x::ys))]

-- Right queue in the output is the queue before the operation
interp : Queue a -> Signal (QueueCommand a) -> Signal ([(QueueOp a, Queue a)], Queue a)
interp q0 commandSig =
  let exec command (ss, _) = let q = snd (last ss) in
    case command of
      Put x -> (execPut x q, q)
      Pop   -> (execPop q, q)
  in
  foldp exec ([(Nop, q0)], q0) commandSig

type Point = { x : Float, y : Float }

type QueueGraphic a =
  { stacks     : (StackGraphic a, StackGraphic a)
  , looseBlock : Maybe (BlockGraphic a)
  }

type StackGraphic a = [a]

type BlockGraphic a = { pos : Point, block : a }

-- Graphics code.
blockSideLength : Float
blockSideLength = 100

stackBlock : a -> Int -> Form
stackBlock x n =
  let sq = group [filled blue (square blockSideLength), toForm (centered (toText (show x)))]
  in moveY (toFloat n * blockSideLength) sq

stackForm : StackGraphic a -> Form
stackForm bs =
  let len = length bs
  in group (indexedMap (\i x -> stackBlock x (len - 1 - i)) bs)

looseBlockForm : BlockGraphic a -> Form
looseBlockForm {pos, block} = move (pos.x, pos.y) (stackBlock block 0)

stackShift = 130

queueForm : QueueGraphic a -> Form
queueForm { stacks, looseBlock } =
  let (l, r) = stacks
      bform  = case looseBlock of { Nothing -> []; Just b -> [looseBlockForm b] }
  in
  group <| [stackForm l, moveX stackShift (stackForm r)] ++ bform

-- queueOpAnim : (QueueOp a, Queue a) -> Seq (QueueGraphic a)

blockFallTime = 700 * millisecond

linearly : Time -> Float -> Float -> (Time -> Float)
linearly dur start stop = \t -> if t >= dur then stop else start + (stop - start) * (t / dur)

blocksHeight : Int -> Float
blocksHeight n = toFloat n * blockSideLength

newBlockPos : Int -> Time -> Point
newBlockPos stackHeight = 
  let yFinal   = blocksHeight stackHeight
      yInitial = 1000
  in
  (\y -> {x = stackShift, y = y}) << (linearly blockFallTime yInitial yFinal)

-- The arg should be the queue before the put
-- Duration: 2 seconds
putRightAnim : a -> Queue a -> Seq (QueueGraphic a)
putRightAnim x q =
  let blockPos = newBlockPos (length (snd q))
  in for blockFallTime (\t -> {stacks = q, looseBlock = Just {pos = blockPos t, block = x}})

-- The arg should be the queue after the pop
-- Duration: 2 seconds
popLeftAnim : a -> Queue a -> Seq (QueueGraphic a)
popLeftAnim x q =
  let blockFlyTime = 700 * millisecond
      blockY = blocksHeight (length (fst q))
      blockPos = (\x -> {x = x, y = blockY}) << linearly blockFlyTime 0 (-500)
  in
  for blockFlyTime (\t -> {stacks = q, looseBlock = Just {pos = blockPos t, block = x}})

-- TODO: Perhaps these functions should be given the queue and modify it
-- as it should. I.e., exec and make the animation at the same time.
-- The arg should be the queue with the moving block on neither half.
-- Duration: 2 seconds
rightToLeftAnim : a -> Queue a -> Seq (QueueGraphic a)
rightToLeftAnim x (l, r) =
  let (n_l, n_r) = (length l, length r)
      (h_l, h_r) = (blocksHeight n_l, blocksHeight n_r)
      blockPos   = runSeq (
        if n_l > n_r
        then upBlockPos h_r h_l stackShift >>> leftBlockPos stackShift 0 h_l
        else leftBlockPos stackShift h_l h_r >>> upBlockPos h_r h_l 0)
  in
  for (1 * second) (\t -> {stacks = (l, r), looseBlock = Just {pos = blockPos t, block = x}})

upBlockPos   y0 yFinal x = for (0.5 * second) <| (\y -> {x=x, y=y}) << linearly (0.5 * second) y0 yFinal
leftBlockPos x0 xFinal y = for (0.5 * second) <| (\x -> {x=x, y=y}) << linearly (0.5 * second) x0 xFinal

animate : Signal ([(QueueOp a, Queue a)], Queue a) -> Signal (Seq (QueueGraphic a))
animate =
  let toSeq q (op, q') =
    case op of
      PutRight x    -> putRightAnim x q
      PopLeft x     -> popLeftAnim x q'
      RightToLeft x -> let (_::l,r) = q' in rightToLeftAnim x (l, r)
      Nop           -> forever (\_ -> { stacks = q', looseBlock = Nothing })
      EmptyError    -> forever (\_ -> { stacks = q', looseBlock = Nothing })
  in
  lift (\(ops, q) -> concatSeq (map (toSeq q) ops))

draw : Signal (Seq (QueueGraphic a)) -> Signal Form
draw s =
  lift2 (\(t0, seq) t -> queueForm <| runSeq seq (t - t0)) (timestamp s) (every (30 * millisecond))


-- TODO: Currently unused
parseCommand : String -> Maybe (QueueCommand Int)
parseCommand =
  let re = regex "push\\((\\d+)\\)|pop" in
  \s ->
    case find All re s of
      []   -> Nothing
      m :: _ -> 
        case m.submatches of
          [Nothing]     -> Just Pop
          (Just x :: _) -> Maybe.map Put (toInt x)

