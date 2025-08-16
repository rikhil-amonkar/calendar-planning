#!/usr/bin/env python3
import itertools
import json

def solve():
    names = ["Eric", "Arnold", "Alice", "Peter"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]
    solutions = []
    
    # Houses are positions 0,1,2,3 corresponding to houses 1,2,3,4.
    for name_perm in itertools.permutations(names):
        # Clue 1: Alice is in the second house (index 1)
        if name_perm[1] != "Alice":
            continue
        for style_perm in itertools.permutations(styles):
            # Clue 5: The person in a Craftsman-style house is Alice.
            try:
                craftsman_index = style_perm.index("craftsman")
            except ValueError:
                continue
            if name_perm[craftsman_index] != "Alice":
                continue

            # Clue 2: The person residing in a Victorian house is directly left of Peter.
            try:
                victorian_index = style_perm.index("victorian")
            except ValueError:
                continue
            # The Victorian house cannot be the last house.
            if victorian_index == 3:
                continue
            if name_perm[victorian_index + 1] != "Peter":
                continue
            
            # Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
            try:
                ranch_index = style_perm.index("ranch")
            except ValueError:
                continue
            peter_index = name_perm.index("Peter")
            if not (peter_index > ranch_index):
                continue

            # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
            arnold_index = name_perm.index("Arnold")
            if not (arnold_index > craftsman_index):
                continue

            solutions.append((name_perm, style_perm))
    return solutions

def main():
    sols = solve()
    if sols:
        name_sol, style_sol = sols[0]
        rows = []
        for i in range(4):
            house_number = str(i+1)
            row = [house_number, name_sol[i], style_sol[i]]
            rows.append(row)
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()