import System.Environment
import Quipper
import Quipper.Libraries.Arith

main :: IO ()
main = do
  [x] <- getArgs
  let c = read x
  print_generic ASCII (q_mult_param (intm 16 c)) (qshape (intm 16 0))
