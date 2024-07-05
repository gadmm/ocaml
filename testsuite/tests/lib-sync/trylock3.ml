(* TEST *)

(* Test Mutex.try_protect *)

let () =
  let m = Mutex.create () in
  (match ignore (Mutex.try_protect m (fun () -> raise Exit)) with
   | _ -> failwith "try_protect1"
   | exception Exit -> ());
  (match Mutex.try_protect m (fun () -> Mutex.try_lock m) with
   | Some true -> failwith "try_lock1"
   | None -> failwith "try_protect2"
   | _ -> ());
  if not (Mutex.try_lock m) then failwith "try_lock2"
