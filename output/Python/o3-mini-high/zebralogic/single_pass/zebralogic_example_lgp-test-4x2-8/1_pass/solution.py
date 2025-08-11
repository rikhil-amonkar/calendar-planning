#!/usr/bin/env python3
import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    houses = [1, 2, 3, 4]  # House numbers (not used in permutation but for ordering)
    names = ["Peter", "Arnold", "Alice", "Eric"]
    colors = ["yellow", "green", "red", "white"]

    solution = None

    # Generate all possible assignments that satisfy the constraints
    for name_perm in permutations(names):
        # Constraint 2: Peter is in the first house.
        if name_perm[0] != "Peter":
            continue

        for color_perm in permutations(colors):
            # Constraint 1: The person whose favorite color is green is in the third house.
            if color_perm[2] != "green":
                continue

            # Constraint 3: There is one house between the person whose favorite color is red and the person who loves yellow.
            if abs(color_perm.index("red") - color_perm.index("yellow")) != 2:
                continue

            # Constraint 5: Eric is the person who loves yellow.
            if name_perm.index("Eric") != color_perm.index("yellow"):
                continue

            # Constraint 4: Arnold is directly left of Eric.
            if name_perm.index("Eric") != name_perm.index("Arnold") + 1:
                continue

            # All constraints satisfied; we found a solution.
            solution = {
                "header": ["House", "Name", "favorite color"],
                "rows": []
            }
            for i in range(4):
                # Houses are numbered from 1 to 4.
                solution["rows"].append([str(i + 1), name_perm[i], color_perm[i]])
            return solution

def main():
    sol = solve_puzzle()
    output = {"solution": sol}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()