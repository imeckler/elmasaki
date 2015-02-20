-- module Queue where

-- This module implements functional Queues as described in Okasaki 1996
-- (http://www.cs.cmu.edu/~rwh/theses/okasaki.pdf) along with types
-- reifying operations on those queues.

import Debug
import Easing(..)
import Time (second)
import Time
import Stage
import Stage(Stage, ForATime, Forever)
import Stage.Infix(..)
import Maybe
import List
import List((::))
import Color(..)
import Graphics.Collage(..)
import Graphics.Element(..)
import Graphics.Input (..)
import Text
import Signal

-- In our quest to achieve good performance, we represent queues as a pair
-- of lists: the first representing the front of the queue, and the second
-- representing the back (in reverse order). The point is that it's easy to
-- perform both of the essential queue operations.
-- 1. Popping an element off the front of the queue (assuming it's non-empty)
--    is as easy as taking the head of the first list in the pair.
-- 2. Pushing an element onto the back of the queue is just consing onto the
--    second list in the pair, since we're representing the back of the queue
--    in reverse.
type alias Queue a = (List a, List a)

empty : Queue a
empty = ([], [])

put : a -> Queue a -> Queue a
put x (xs, ys) = (xs, x::ys)

pop : Queue a -> Maybe (a, Queue a)
pop q = 
  case q of
    ([], [])    -> Nothing
    ([], ys)    -> pop (List.reverse ys, [])
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

type QueueCommand a
  = Put a
  | Pop
  | NoOp

-- and then we build a signal of type `Signal (QueueCommand a)`, which represents the stream
-- of queue commands. For now, let's just suppose we have such a signal.

-- The `QueueCommand`s themselves aren't directly animatable. The `Pop` command in particular
-- could have many different animations associated to it depending on the state of the queue:
-- Sometimes it just pops an element off the left list, sometimes it causes the right list
-- to be reversed and shuffled over to the left list. These two things should of course be
-- animated differently.

-- So, with that in mind, we define the following type, which more directly represents the
-- state of our system (the queue) as our two operations (Pop and Put) are performed on it. 

type PuttingState a = PuttingRight a (Queue a)

type PoppingState a
  = PoppingLeft a (Queue a)
  | RightToLeft a (Queue a)

type Execution a
  = Popping (List (PoppingState a))
  | Putting (List (PuttingState a))
  | NoOpping (Queue a)

first : (a -> a') -> (a, b) -> (a', b)
first f (x, y) = (f x, y)

interpretCommand : QueueCommand a -> Queue a -> (Execution a, Queue a)
interpretCommand qc = case qc of
  Put x -> \q -> first Putting <| record stepPutting (PuttingRight x q)
  Pop   -> \q -> case q of
    ([], [])         -> (NoOpping q, q)
    ([], x::back)    -> first Popping <| record stepPopping (RightToLeft x ([], back))
    (x::front, back) -> first Popping <| record stepPopping (PoppingLeft x (front, back))

interpretExecution : Execution a -> Stage Forever Form
interpretExecution =
  let animWith anim = Stage.sustain << List.foldr1 (<>) << List.map anim in
  \e -> case e of
    Popping pss -> animWith drawPopping pss
    Putting pss -> animWith drawPutting pss
    NoOpping q  -> Stage.stayForever (drawQueue q)

-- Note that if we have a value of type `PoppingState a`, we can always either take a step in the
-- popping algorithm (shuffle the next element from the back queue to the front queue) or finish.
-- With that in mind, we define

type OrDone x a = Done (Queue x) | StillGoing a

stepPopping : PoppingState a -> OrDone a (PoppingState a)
stepPopping ps = case ps of
  PoppingLeft x q             -> Done q
  RightToLeft x (front, back) -> case back of
    []       -> StillGoing (PoppingLeft x (front, back))
    y::back' -> StillGoing (RightToLeft y (x :: front, back'))

-- Similarly, we can define `stepPutting`.

stepPutting : PuttingState a -> OrDone a (PuttingState a)
stepPutting (PuttingRight x (front, back)) = Done (front, x :: back)

-- Now a function which builds up the history of the intermediate states in performing some opertation,
-- as well as returning the queue in its post-operation state.
record : (s -> OrDone a s) -> s -> (List s, Queue a)
record step s = case step s of
  Done q        -> ([s], q)
  StillGoing s' -> let (ss, q) = record step s' in (s :: ss, q)

-- Throwing in a function which animates one step, we get a general description of how to animate an
-- an operation on a queue, by stringing together the animations of the intermediate steps.
animatedSteps
  :  (s -> OrDone a s)
  -> (s -> Stage ForATime Form)
  -> (s -> (Stage Forever Form, Queue a))
animatedSteps step animateStep s =
  let (ss, q) = Debug.watch "record" <| record step s in
  ( List.foldr1 (<>) (List.map animateStep ss) <> Stage.stayForever (drawQueue q)
  , q)

-- Now we put it all together in a function that "executes" commands on a queue
-- to get a new queue and an animation of the execution.

main : Signal Element
main =
  Signal.foldp (\qc (_, q) -> first interpretExecution <| interpretCommand qc q) (Stage.stayForever (drawQueue empty), empty)
    (Signal.subscribe commandChan)
  |> Signal.map fst
  |> (\ss -> Stage.run ss (Time.every 20))
  |> Signal.map (\f -> flow down [collage 500 500 [moveY -190 f], container 500 40 middle <| buttons])

-- Graphics code.
blockSideLength : Float
blockSideLength = 100
halfLength = blockSideLength / 2

backStackX = blockSideLength * 0.75
frontStackX  = -backStackX

heightAt n = toFloat n * blockSideLength

drawBlock x =
  let sty = {defaultLine | join <- Smooth, width <- 10} in
  group
  [ outlined  sty (square blockSideLength)
  , traced sty (segment (-halfLength, -halfLength) (halfLength, halfLength))
  , traced sty (segment (halfLength, -halfLength) (-halfLength, halfLength))
  ]

drawStack : List a -> Form
drawStack xs =
  let n = List.length xs in
  group <|
  List.indexedMap (\i x ->
    drawBlock x |> moveY  (toFloat (n - 1 - i) * blockSideLength))
    xs

drawQueue : Queue a -> Form
drawQueue (front, back) = 
  group
  [ drawStack front |> moveX frontStackX
  , drawStack back  |> moveX backStackX
  ]

drawPutting : PuttingState a -> Stage ForATime Form
drawPutting (PuttingRight x ((_, back) as q)) =
  let qDrawing   = drawQueue q
      dropHeight = 1000
      hitHeight  = blockSideLength * toFloat (List.length back)
      h t        = dropHeight - (t/20)^2
      dur        = 20 * sqrt (dropHeight - hitHeight)
  in
  Stage.for dur (\t -> group [drawBlock x |> move (backStackX, h t), qDrawing])

drawPopping : PoppingState a -> Stage ForATime Form
drawPopping ps = case ps of
  RightToLeft x q -> drawRightToLeft x q
  PoppingLeft x q -> drawPoppingLeft x q

drawRightToLeft : a -> Queue a -> Stage ForATime Form
drawRightToLeft x ((front, back) as q) =
  let dur         = 0.5 * second
      qDrawing    = drawQueue q
      backHeight  = heightAt (List.length back)
      frontHeight = heightAt (List.length front)
      up          = Stage.for dur <| ease easeInOutQuad float backHeight frontHeight dur
      left        = Stage.for dur <| ease easeInOutQuad float backStackX frontStackX dur
      pos         = 
        if backHeight > frontHeight
        then Stage.map (\x -> (x, backHeight)) left <> Stage.map (\y -> (frontStackX, y)) up
        else Stage.map (\y -> (backStackX, y)) up <> Stage.map (\x -> (x, frontHeight)) left
  in
  Stage.map (\p -> group [qDrawing, move p (drawBlock x)]) pos

drawPoppingLeft : a -> Queue a -> Stage ForATime Form
drawPoppingLeft v ((front, _) as q) =
  let y        = heightAt (List.length front)
      qDrawing = drawQueue q
      dur      = 0.6 * second
  in
  Stage.map (\x -> group [qDrawing, drawBlock v |> move (x, y)])
    (Stage.for dur (ease easeInQuart float frontStackX -1000 dur))

-- tying it all together
commandChan : Signal.Channel (QueueCommand a)
commandChan = Signal.channel NoOp

buttons : Element
buttons =
  flow right
  [ button (Signal.send commandChan (Put "x")) "Put"
  , button (Signal.send commandChan Pop) "Pop"
  ]
