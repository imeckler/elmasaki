module Main where

import Queue (..)
import Graphics.Input.Field
import Graphics.Input (..)

pushes : Input ()
pushes = input ()

pops : Input ()
pops = input ()

buttons : Element
buttons = flow right [button pushes.handle () "Push", button pops.handle () "Pop"]

-- queueSignal : Signal (Queue Int)
queueSignal =
  merge (lift (\_ -> Put 1) pushes.signal) (lift (\_ -> Pop) pops.signal)
  |> interp ([], [])

drawing : Signal Element
drawing =
  queueSignal
  |> animate
  |> draw
  |> lift (\x -> flow down [collage 800 700 [moveY -200 x], buttons])

main = drawing

