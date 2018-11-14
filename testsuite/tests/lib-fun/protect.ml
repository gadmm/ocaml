(* TEST
*)

let does_raise f x =
  try
    f x;
    false
  with _ -> true

let double_raise () =
  let f () = raise Exit in
  try
    Fun.protect ~acquire:(fun () -> ()) ~release:f f ()
  with
  | Exit -> ()

let _ =
  assert(does_raise double_raise ())
