import Control.App.Console

interface Random e where
  getRnd : App {l} e Integer

Has [State Integer] e => Random e where
  getRnd
      = do modify (\x => (1103515245 * x + 12345) `mod` 4294967296)
           get

initRnd : (seed : Integer) -> (Random e => App e a) -> App e a
initRnd seed p = new seed p

diceRoll : Has [Random, Console] e => App e ()
diceRoll
    = do num <- getRnd
         putStrLn (show $ num `mod` 6 + 1)
         x <- getStr
         diceRoll

diceRolls : IO ()
diceRolls = run (initRnd 1234567890 $ diceRoll)
