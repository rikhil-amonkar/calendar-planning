#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    houses = ["1", "2", "3"]
    names = ["Eric", "Peter", "Arnold"]
    mothers = ["Holly", "Aniya", "Janelle"]
    foods = ["pizza", "grilled cheese", "spaghetti"]

    solution = None

    # Iterate over all permutations assignments for names, mothers, and foods.
    for names_perm in itertools.permutations(names):
        for mothers_perm in itertools.permutations(mothers):
            # Clue 4: Peter's mother must be Holly.
            peter_house = names_perm.index("Peter")
            if mothers_perm[peter_house] != "Holly":
                continue

            for foods_perm in itertools.permutations(foods):
                # Constraint: Clue 3 says: The person who loves eating grilled cheese is Eric.
                try:
                    grilled_index = foods_perm.index("grilled cheese")
                except ValueError:
                    continue
                if names_perm[grilled_index] != "Eric":
                    continue

                # Constraint: Clue 2: The person who loves grilled cheese is directly left of the person whose mother's name is Aniya.
                # That means the house immediately to the right of the house with grilled cheese must have mother "Aniya".
                if grilled_index == 2:  # cannot be in the rightmost house
                    continue
                if mothers_perm[grilled_index + 1] != "Aniya":
                    continue

                # Constraint: Clue 1: The person who loves spaghetti and Peter are next to each other.
                # We interpret "loves the spaghetti eater" as the person whose food is spaghetti.
                try:
                    spaghetti_index = foods_perm.index("spaghetti")
                except ValueError:
                    continue
                if abs(spaghetti_index - names_perm.index("Peter")) != 1:
                    continue

                # If all constraints are met, we've found a solution.
                solution = []
                for i in range(3):
                    solution.append([houses[i], names_perm[i], mothers_perm[i], foods_perm[i]])
                return {"solution": {"header": ["House", "Name", "Mother", "Food"], "rows": solution}}
    return None

if __name__ == '__main__':
    sol = solve_puzzle()
    if sol is None:
        print(json.dumps({"solution": {}}))
    else:
        print(json.dumps(sol))