import json
from itertools import permutations

def solve_puzzle():
    # Houses are ordered left (1) to right (2)
    houses = [1, 2]

    # Attributes
    Names = ["Eric", "Arnold"]
    Children = ["Bella", "Fred"]
    Foods = ["grilled cheese", "pizza"]

    solutions = []

    # Iterate over all possible assignments
    for name_perm in permutations(Names):
        for child_perm in permutations(Children):
            for food_perm in permutations(Foods):
                # Constraint 1: The person who is a pizza lover is Arnold.
                valid = True
                for i in range(len(houses)):
                    if name_perm[i] == "Arnold" and food_perm[i] != "pizza":
                        valid = False
                        break
                    if food_perm[i] == "pizza" and name_perm[i] != "Arnold":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 2:
                # "The person who loves eating grilled cheese is directly left of
                #  the person whose child is named Fred."
                idx_grilled = food_perm.index("grilled cheese")
                idx_fred = child_perm.index("Fred")
                if not (idx_grilled == idx_fred - 1):
                    continue

                solutions.append((name_perm, child_perm, food_perm))

    if not solutions:
        raise ValueError("No solution found")

    # Assuming a unique solution for this puzzle
    name_sol, child_sol, food_sol = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": [
                ["1", name_sol[0], child_sol[0], food_sol[0]],
                ["2", name_sol[1], child_sol[1], food_sol[1]],
            ],
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False))