module DoorL

import Control.App
import Control.App.Console

data DoorState = OPEN | CLOSED

data Door : DoorState -> Type where
     MkDoor : (d : DoorState) -> Door d

CheckState : Bool -> DoorState
CheckState ok = if ok then OPEN else CLOSED

interface DoorI e where
  newDoor : AppL One e (Door CLOSED)
  openDoor : (1 d : Door CLOSED) ->
             AppL One e (Res Bool (\ok => Door (CheckState ok)))
  closeDoor : (1 d : Door OPEN) -> AppL One e (Door CLOSED)
  deleteDoor : (1 d : Door CLOSED) -> App {l} e ()

Has [Console] e => DoorI e where
  newDoor
      = do app $ putStrLn "Door created"
           pure1 (MkDoor _)

  openDoor (MkDoor _) = pure1 (True @@ MkDoor _)
  closeDoor (MkDoor _) = pure1 (MkDoor _)

  deleteDoor (MkDoor _)
      = putStrLn "Door destroyed"

doorProg : Has [Console, DoorI] e => 
           App e ()
doorProg
    = appL $ do
         d <- newDoor
         True @@ d <- openDoor d
              | False @@ d => do app $ putStrLn "Opening failed"
                                 app $ deleteDoor d
         app $ putStrLn "Door opened"
         d <- closeDoor d 
         app $ putStrLn "Door closed"
         app $ deleteDoor d

foo : IO ()
foo = run doorProg
