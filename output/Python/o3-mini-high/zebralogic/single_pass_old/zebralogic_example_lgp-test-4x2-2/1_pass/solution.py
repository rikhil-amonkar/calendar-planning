#!/usr/bin/env python3
import itertools
import json

def solve_zebra_puzzle():
    # Define the possibilities for each attribute
    houses = [1, 2, 3, 4]
    names = ["Arnold", "Peter", "Eric", "Alice"]
    styles = ["victorian", "ranch", "colonial", "craftsman"]

    solutions = []
    # Try all permutations for assigning names
    for names_perm in itertools.permutations(names):
        # Constraint 3: Eric is in the third house.
        if names_perm[2] != "Eric":
            continue
        # Constraint 4: Arnold is in the fourth house.
        if names_perm[3] != "Arnold":
            continue

        # Try all permutations for assigning house styles
        for styles_perm in itertools.permutations(styles):
            # Constraint 1: Eric is the person in a Craftsman-style house.
            if styles_perm[2] != "craftsman":
                continue

            # Constraint 2: The person in a ranch-style home is directly left of the person residing in a Victorian house.
            ranch_index = styles_perm.index("ranch")
            victorian_index = styles_perm.index("victorian")
            if victorian_index != ranch_index + 1:
                continue

            # Constraint 5: The person residing in a Victorian house is Alice.
            if names_perm[victorian_index] != "Alice":
                continue

            # All constraints satisfied, store the solution.
            solution = []
            for i in range(4):
                solution.append([str(houses[i]), names_perm[i], styles_perm[i]])
            solutions.append(solution)

    return solutions

def main():
    sol = solve_zebra_puzzle()
    # Assume a unique solution exists and select the first one.
    if sol:
        result = {
            "solution": {
                "header": ["House", "Name", "Style"],
                "rows": sol[0]
            }
        }
    else:
        result = {"solution": None}
    print(json.dumps(result))

if __name__ == "__main__":
    main()