import Quipper
import Quipper.Libraries.Arith
import Quipper.Libraries.QFTAdd

main :: IO ()
main = print_generic ASCII qft_add_in_place example_num example_num
  where example_num = qshape (intm 16 0)
