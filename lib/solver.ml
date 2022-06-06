open Z3

type puzzle = int array array
type consts_table = (string, Expr.expr) Hashtbl.t

let line2puzzle (line: string) =
  let rec construct_puzzle constructed_puzzle line i =
    if i = 81 then
      ()
    else
      let elem = int_of_string (String.sub line i 1) in
      let x = i / 9 in
      let y = i mod 9 in
      let row = Array.get constructed_puzzle x in
      begin
        Array.set row y elem;
        construct_puzzle constructed_puzzle line (i + 1)
      end
  in
  let puzzle = Array.make_matrix 9 9 0 in
  begin
    construct_puzzle puzzle line 0;
    puzzle
  end

let print_puzzle custom_print (p : puzzle) =
  let rec print_puzzle_cells (p : puzzle) (row : int) (col : int) =
    begin
      (if row mod 3 = 0 && col = 0 then
         print_string ("+" ^ (String.make 20 '-') ^ "\n")
       else
         ());
      (if col mod 3 = 0 then
         print_char '|'
       else
         ());
      (let value =  p.(row).(col) in
      if value = 0 then
        custom_print row col
      else
        print_int value);
      print_char ' ';
      if col < 8 then
        print_puzzle_cells p row (col + 1)
      else if col = 8 then
        if row < 8 then
          begin
            print_char '\n';
            print_puzzle_cells p (row + 1) 0
          end
        else
          ()
    end
  in
  print_puzzle_cells p 0 0

let load_puzzles (filename: string) =
  (* load puzzle *)
  let rec read_process_lines puzzles in_chan =
    let line = 
      try (Some (input_line in_chan)) with
      | End_of_file -> None
    in
    match line with
    | None -> close_in in_chan; List.rev puzzles
    | Some nums ->
      let processed_puzzle = line2puzzle (String.sub nums 0 81) in
      read_process_lines (processed_puzzle::puzzles) in_chan
  in
  read_process_lines [] (open_in filename)


let mk_const_name (row : int) (col : int) = "c" ^ (string_of_int row) ^ (string_of_int col) 

let solve_puzzle (p : puzzle) =
  let ctx = mk_context [] in
  let solver = Solver.mk_simple_solver ctx in
  let (c_table: consts_table) = Hashtbl.create 81 in

  let const_exists (row : int) (col : int) = Hashtbl.mem c_table (mk_const_name row col) in
  let get_const (row : int) (col: int) = Hashtbl.find c_table (mk_const_name row col) in
  let create_const (row : int) (col : int) =
    let const_name = mk_const_name row col in
    let new_const = Arithmetic.Integer.mk_const_s ctx const_name in
    begin
      Hashtbl.add c_table const_name new_const; 
      new_const
    end
  in
  let get_or_create_const (row : int) (col : int) =
    if const_exists row col then 
      get_const row col
    else
      create_const row col
  in
  let create_all_constraints (p : puzzle) =
    let create_cell_with_constraints (cell_row : int) (cell_col : int) (value : int) =
      if value = 0 then
        let cell_const = get_or_create_const cell_row cell_col in
        let rec create_row_constraints (col : int) =
          if col = 9 then () else
          if col = cell_col then create_row_constraints (col + 1) else
            let other_cell_value = p.(cell_row).(col) in
            let other_cell_expr =
              if other_cell_value = 0 then
                get_or_create_const cell_row col
              else
                Arithmetic.Integer.mk_numeral_i ctx other_cell_value
            in
            let assertion = Boolean.mk_not ctx (Boolean.mk_eq ctx other_cell_expr cell_const) in
            begin
              Solver.add solver [assertion];
              create_row_constraints (col + 1)
            end
        in
        let rec create_col_constraints (row : int) =
          if row = 9 then () else
          if row = cell_row then create_col_constraints (row + 1) else
            let other_cell_value = p.(row).(cell_col) in
            let other_cell_expr =
              if other_cell_value = 0 then
                get_or_create_const row cell_col
              else
                Arithmetic.Integer.mk_numeral_i ctx other_cell_value
            in
            let assertion = Boolean.mk_not ctx (Boolean.mk_eq ctx other_cell_expr cell_const) in
            begin
              Solver.add solver [assertion];
              create_col_constraints (row + 1)
            end
        in
        let create_box_constraints (start_row : int) (start_col : int) =
          let rec aux (row : int) (col : int) =
            if row = cell_row && col = cell_col then () else
            if row - start_row = 3 then () else
              let other_cell_value = p.(row).(col) in
              let other_cell_expr =
                if other_cell_value = 0 then
                  get_or_create_const row col
                else
                  Arithmetic.Integer.mk_numeral_i ctx other_cell_value
              in
              let assertion = Boolean.mk_not ctx (Boolean.mk_eq ctx other_cell_expr cell_const) in
              begin
                Solver.add solver [assertion];
                if col - start_col = 2 then
                  aux (row + 1) start_col
                else
                  aux row (col + 1)
              end
          in
          aux start_row start_col
        in
        let create_bounds_constraints () =
          let ge1 = Arithmetic.mk_ge ctx cell_const (Arithmetic.Integer.mk_numeral_i ctx 1) in
          let le9 = Arithmetic.mk_le ctx cell_const (Arithmetic.Integer.mk_numeral_i ctx 9) in
          Solver.add solver [ge1; le9]
        in
        begin
          create_row_constraints 0;
          create_col_constraints 0;
          create_box_constraints ((cell_row/3)*3) ((cell_col/3)*3);
          create_bounds_constraints ()
        end
      else
        ()
    in
    Array.iteri (fun row_index row ->
              Array.iteri (fun col_index cell_value ->
                  create_cell_with_constraints row_index col_index cell_value
                ) row
            ) p
  in
  begin
    create_all_constraints p;
    let status = Solver.check solver [] in
    (c_table, status, Solver.get_model solver)
  end

let load_and_solve () =
  set_global_param "unsat_core" "true";
  set_global_param "proof" "true";
  let puzzles = load_puzzles "easy10.sdm" in
  let puzzle1 = List.nth puzzles 0 in
  let c_table , _, model = solve_puzzle puzzle1 in
  (c_table, model)
    

let print_solution (model : Model.model) (c_table : consts_table) (p : puzzle) =
  print_puzzle
    (fun row col -> 
      let const_name = mk_const_name row col in
      let const = Hashtbl.find c_table const_name in
      let maybe_cell_value = Model.evaluate model const false in
      let cell_value_string = match maybe_cell_value with
      | None -> "_"
      | Some expr -> Expr.to_string expr
      in
      print_string ("\027[0;32m" ^ cell_value_string ^ "\027[0;06m"))
    p


let print_loaded_puzzle () =
  let puzzles = load_puzzles "easy10.sdm" in
  let puzzle1 = List.nth puzzles 0 in
  print_puzzle (fun _ _ -> print_int 0) puzzle1

(*let solve_puzzle = puzzle -> puzzle*)
