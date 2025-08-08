import sys
import os
import pickle
import subprocess

# Serialized Z3 solver code
z3_code = r"""
import os
import sys
from z3 import Solver, Int, Distinct, sat

def solve():
    # Initialize solver
    s = Solver()
    grid = [[Int(f'cell_{r}_{c}') for c in range(9)] for r in range(9)]
    
    # Cell constraints: 1-9 values
    for r in range(9):
        for c in range(9):
            s.add(grid[r][c] >= 1, grid[r][c] <= 9)
    
    # Row/column uniqueness
    for i in range(9):
        s.add(Distinct([grid[i][c] for c in range(9)]))
        s.add(Distinct([grid[r][i] for r in range(9)]))
    
    # 3x3 box uniqueness
    for r in range(0, 9, 3):
        for c in range(0, 9, 3):
            s.add(Distinct([grid[r+dr][c+dc] for dr in range(3) for dc in range(3)]))
    
    # Puzzle definition
    puzzle = [
        [5, 3, 0, 0, 7, 0, 0, 0, 0],
        [6, 0, 0, 1, 9, 5, 0, 0, 0],
        [0, 9, 8, 0, 0, 0, 0, 6, 0],
        [8, 0, 0, 0, 6, 0, 0, 0, 3],
        [4, 0, 0, 8, 0, 3, 0, 0, 1],
        [7, 0, 0, 0, 2, 0, 0, 0, 6],
        [0, 6, 0, 0, 0, 0, 2, 8, 0],
        [0, 0, 0, 4, 1, 9, 0, 0, 5],
        [0, 0, 0, 0, 8, 0, 0, 7, 9]
    ]
    
    # Apply puzzle constraints
    for r in range(9):
        for c in range(9):
            if puzzle[r][c] != 0:
                s.add(grid[r][c] == puzzle[r][c])
    
    # Solve and return solution
    if s.check() == sat:
        model = s.model()
        return [[model.evaluate(grid[r][c]).as_long() for c in range(9)] for r in range(9)]
    return None

# Execute solver and serialize result
result = solve()
sys.stdout.buffer.write(pickle.dumps(result))
"""

def main():
    # Create clean subprocess with redirected I/O
    with subprocess.Popen(
        [sys.executable, "-c", z3_code],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        bufsize=0
    ) as proc:
        # Receive serialized result
        solution = pickle.load(proc.stdout)
        return solution

# Entry point - solution is computed but not printed
if __name__ == "__main__":
    solution = main()
    # Solution is available in 'solution' variable