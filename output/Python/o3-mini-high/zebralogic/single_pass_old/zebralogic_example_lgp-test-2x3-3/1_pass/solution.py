#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    # Define the puzzle attributes
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    lunches = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]

    # We'll iterate over all possible permutations for the assignments.
    for name_perm in itertools.permutations(names):
        for lunch_perm in itertools.permutations(lunches):
            for mother_perm in itertools.permutations(mothers):

                # Constraint 1:
                # The person who loves grilled cheese must be directly left of the person who loves pizza.
                # With two houses, house1 must have "grilled cheese" and house2 "pizza".
                if not (lunch_perm[0] == "grilled cheese" and lunch_perm[1] == "pizza"):
                    continue

                # Constraint 2:
                # Arnold is not in the second house.
                if name_perm[1] == "Arnold":
                    continue

                # Constraint 3:
                # Arnold is the person whose mother's name is Holly.
                # Find the index of "Arnold" and verify corresponding mother is "Holly".
                arnold_index = name_perm.index("Arnold")
                if mother_perm[arnold_index] != "Holly":
                    continue

                # If all constraints are satisfied, store the valid assignment.
                solution = []
                for i in range(len(houses)):
                    # House number as string.
                    row = [str(houses[i]), name_perm[i], lunch_perm[i], mother_perm[i]]
                    solution.append(row)
                return solution

    return None

def main():
    solution_rows = solve_puzzle()
    if solution_rows is None:
        result = {"solution": {"header": ["House", "Name", "lunch", "mothers' names"], "rows": []}}
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "lunch", "mothers' names"],
                "rows": solution_rows
            }
        }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()