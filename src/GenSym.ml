module type WStr = sig val v : string end ;;

module Make (Pref : sig val v : string end) = struct
  let idx = ref 0
  let reset () = idx := 0
  let gen_sym () = 
    let curr = !idx in 
    idx := curr + 1 ;
    Format.sprintf "%s_%i" Pref.v curr
end 
