open Program
open Parser

let starts st line =
  String.length line >= String.length st &&
    (String.sub line 0 (String.length st)) = st
;;

(* Read the program from a filename provided on the command line *)
if Array.length Sys.argv < 2 then () else
  let infile = open_in Sys.argv.(1) in
  let first_line = input_line infile in (* Allow the unix #! trick on the first line, just for fun *)
  let rec read_loop acc =
    let next_line = try Some (input_line infile) with End_of_file -> None in
    match next_line with
    | Some s -> read_loop (s::acc)
    | None -> List.rev acc in
  let progLines = read_loop (if starts "#!" first_line then [] else [first_line]) in
  let progString = String.concat "\n" progLines in
  (* Parse the program...*)
  let progExpr = progString |> wordlist |> tokens |> parse_program in
  (* Type check the program; we don't actually care about its type, just that it is valid. *)
  let t = typeof progExpr [] in
  (* Run the program. *)
  let _ = eval progExpr [] in ()
