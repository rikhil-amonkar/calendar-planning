#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3]  # House numbers: 1 to 3 (left to right)
    names = ["Eric", "Arnold", "Peter"]
    heights = ["short", "very short", "average"]

    # We'll search over all assignments (permutations) of names and heights to houses.
    for perm_names in itertools.permutations(names):
        # Constraint: Eric is not in the first house and Arnold is not in the first house.
        if perm_names[0] in ["Eric", "Arnold"]:
            continue
        for perm_heights in itertools.permutations(heights):
            valid = True
            # Constraint: Eric must be "very short".
            for i in range(3):
                if perm_names[i] == "Eric" and perm_heights[i] != "very short":
                    valid = False
                    break
            if not valid:
                continue
            # Constraint: The person who is very short is somewhere to the left of the person who is short.
            try:
                idx_very_short = perm_heights.index("very short")
                idx_short = perm_heights.index("short")
            except ValueError:
                continue
            if idx_very_short >= idx_short:
                continue
            # When we pass all constraints, we found a valid solution.
            solution = []
            for i in range(3):
                # House number as string, then Name, then Height.
                solution.append([str(houses[i]), perm_names[i], perm_heights[i]])
            return solution
    return None

def main():
    solution_rows = solve_puzzle()
    output = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": solution_rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()