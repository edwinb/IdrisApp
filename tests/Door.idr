module Door

import Control.App
import Control.App.Console

data DoorState = OPEN | CLOSED

data Door : DoorState -> Type where
     MkDoor : (d : DoorState) -> Door d

interface DoorI e where
  newDoor : (1 prog : (1 d : Door CLOSED) -> App {l} e ()) -> App {l} e ()
  deleteDoor : (1 d : Door CLOSED) -> App {l} e ()

Has [Console] e => DoorI e where
  newDoor f
      = let (>>=) = bindL in
            do putStrLn "Door created"
               f (MkDoor CLOSED)
  deleteDoor (MkDoor _)
      = do putStrLn "Door destroyed"
           pure ()

openDoor : (1 d : Door CLOSED) ->
           Res Bool (\ok => Door (if ok then OPEN else CLOSED))
openDoor (MkDoor _) = True @@ MkDoor _

closeDoor : (1 d : Door OPEN) -> Door CLOSED
closeDoor (MkDoor _) = MkDoor _

doorProg : Has [Console, DoorI] e => 
           App e ()
doorProg
    = let (>>=) = bindL in
        newDoor $ \d =>
          do let True @@ d = openDoor d
                    | False @@ d => do putStrLn "Opening failed"
                                       deleteDoor d
             putStrLn "Door opened"
             let d = closeDoor d 
             putStrLn "Door closed"
             deleteDoor d

foo : IO ()
foo = run doorProg
