# Sudoku SAT Solver

A sudoku solver that uses the Z3 SMT solver to find solutions to Sudoku puzzles.

Build:

```
dune build
```

Run:

```
dune exec smt_sudoku [puzzles_file] [puzzle_index]
```

Example:

```
dune exec smt_sudoku SUPER160.sdm 0
```

TODOs:
- Use `distinct` constraint on cells instead of iterating over all rows and columns to build constraints. Less number of constraints.


