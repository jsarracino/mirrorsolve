type srt_smt = 
  | Smt_bv of int option
  | Smt_int
  | Smt_bool 
  | Custom_sort of string

val valid_sort : srt_smt -> bool
val pretty_sort : srt_smt -> string