open Smt_sudoku


let print_usage () =
    Printf.printf "Usage: %s file_name puzzle_index\n" Sys.argv.(0)


let _ =
    if Array.length Sys.argv = 3 then
        Solver.load_solve_print Sys.argv.(1) (int_of_string Sys.argv.(2))
    else
        print_usage ()

