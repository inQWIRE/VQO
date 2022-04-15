import Quipper
import Quipper.Libraries.Arith

main :: IO ()
main = print_generic ASCII (q_mult_param (intm 16 38168)) (qshape (intm 16 0))
