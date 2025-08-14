#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    houses = ["1", "2"]
    names = ["Eric", "Arnold"]
    styles = ["victorian", "colonial"]
    
    solutions = []
    
    # Generate all permutations for names and styles
    for name_perm in itertools.permutations(names):
        # Clue 2: Eric is in the first house.
        if name_perm[0] != "Eric":
            continue
        
        for style_perm in itertools.permutations(styles):
            # Clue 1: The person residing in a Victorian house is somewhere to the left of 
            # the person living in a colonial-style house.
            if style_perm.index("victorian") < style_perm.index("colonial"):
                # Build solution rows for houses
                rows = []
                for i in range(len(houses)):
                    rows.append([houses[i], name_perm[i], style_perm[i]])
                solutions.append(rows)
    
    # Assuming a unique solution exists, return the first valid solution.
    if solutions:
        return solutions[0]
    return None

def main():
    solution_rows = solve_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "Style"],
            "rows": solution_rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()