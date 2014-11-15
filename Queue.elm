module Queue where

import Sequence (..)
import Regex (..)
import Maybe
import String (toInt)
import Debug

type Queue a = ([a], [a])

data QueueInstr a
  = Put a
  | Pop

data QueueOp a
  = PutRight a
  | PopLeft a
  | RightToLeft a
  | EmptyError
  | Nop

parseInstr : String -> Maybe (QueueInstr Int)
parseInstr =
  let re = regex "push\\((\\d+)\\)|pop" in
  \s ->
    case find All re s of
      []   -> Nothing
      m :: _ -> 
        case m.submatches of
          [Nothing]     -> Just Pop
          (Just x :: _) -> Maybe.map Put (toInt x)

put : a -> Queue a -> Queue a
put x (xs, ys) = (xs, x::ys)

pop : Queue a -> Maybe (a, Queue a)
pop q = 
  case q of
    ([], [])    -> Nothing
    ([], ys)    -> pop (reverse ys, [])
    (x::xs, ys) -> Just (x, (xs, ys))

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

-- Right queue is the queue before the operation
interp : Queue a -> Signal (QueueInstr a) -> Signal ([(QueueOp a, Queue a)], Queue a)
interp q0 instrSig =
  let exec instr (ss, _) = let q = snd (last ss) in
    case instr of
      Put x -> (execPut x q, q)
      Pop   -> (execPop q, q)
  in
  foldp exec ([(Nop, q0)], q0) instrSig

type Point = { x : Float, y : Float }

type QueueGraphic a =
  { stacks     : (StackGraphic a, StackGraphic a)
  , looseBlock : Maybe (BlockGraphic a)
  }

type StackGraphic a = [a]

type BlockGraphic a = { pos : Point, block : a }

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
  let blockPos = Debug.watch "rightpos" << newBlockPos (length (snd q))
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
  let (n_l, n_r) = Debug.watch "lens" (length l, length r)
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
  lift2 (\(t0, seq) t -> let d = Debug.watch "diff" (t - t0) in queueForm <| runSeq seq d) (timestamp s) (every (30 * millisecond))

{-
Signal (Float -> QueueGraphic a)
  zipWith ticks to get
  Signal (QueueGraphic a)
    map draw to get
      Signal Picture
-}

-- draw : Signal 

