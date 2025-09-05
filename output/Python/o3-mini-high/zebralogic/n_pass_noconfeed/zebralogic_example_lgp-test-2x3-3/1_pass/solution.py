import itertools
import json

def solve_puzzle():
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    foods = ["grilled cheese", "pizza"]
    mothers = ["Holly", "Aniya"]

    # Iterate over all possible assignments (permutations) for names, foods, and mothers.
    for name_perm in itertools.permutations(names):
        for food_perm in itertools.permutations(foods):
            for mother_perm in itertools.permutations(mothers):
                # Constraint 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
                # For two houses, this means house 1 must be "grilled cheese" and house 2 must be "pizza".
                if not (food_perm[0] == "grilled cheese" and food_perm[1] == "pizza"):
                    continue

                # Constraint 2: Arnold is not in the second house.
                if name_perm[1] == "Arnold":
                    continue

                # Constraint 3: Arnold is the person whose mother's name is Holly.
                # Find index of "Arnold" in the names permutation and check if at the same index the mother is "Holly".
                arnold_index = name_perm.index("Arnold")
                if mother_perm[arnold_index] != "Holly":
                    continue

                # If all constraints are satisfied, prepare the list of houses.
                solution_rows = []
                for i in range(len(houses)):
                    # Each house row should be a list: ["House", "Name", "Food", "Mother"]
                    # House numbers are to be output as strings.
                    row = [str(houses[i]), name_perm[i], food_perm[i], mother_perm[i]]
                    solution_rows.append(row)

                # Build the solution dictionary with the exact structure.
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Food", "Mother"],
                        "rows": solution_rows
                    }
                }
                return solution
    return None

if __name__ == "__main__":
    result = solve_puzzle()
    if result is not None:
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": {"header": ["House", "Name", "Food", "Mother"], "rows": []}}, indent=2))