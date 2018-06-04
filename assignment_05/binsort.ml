open Printf
open Binsort_core
    
  let read_oint () = try Some (read_int()) with Failure "int_of_string" -> None;;

  let rec print_list (ms : int list) =
    match ms with
      | Nil -> printf "\n"
      | Cons (m, ms') -> 
        printf "%d " m;
        print_list ms';;

  let rec get_list acc =
    match read_oint() with
    | Some x -> get_list (Cons (x, acc))
    | None -> printf "Sorted list\n"; print_list (binsort acc);;

  let () = get_list Nil;;

      

