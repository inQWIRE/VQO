import Quipper
import Quipper.Libraries.Arith

main :: IO ()
main = print_generic ASCII q_moddiv_unsigned_in_place example_num example_num
  where example_num = qshape (intm 16 0)
