import Quipper
import Quipper.Libraries.Arith

main :: IO ()
main = print_generic ASCII q_mult example_num example_num
  where example_num = qshape (intm 16 0)
