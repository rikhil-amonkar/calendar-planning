import itertools
import json

def solve_puzzle():
    # Puzzle parameters
    houses = [1, 2]  # House numbers from left to right
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]

    solutions = []

    # Iterate over all possible assignments
    for name_perm in itertools.permutations(names):
        # Constraint 2: Arnold is not in the first house.
        if name_perm[0] == "Arnold":
            continue

        for food_perm in itertools.permutations(foods):
            # Constraint 1: The person who is a pizza lover is in the second house.
            if food_perm[1] != "pizza":
                continue

            # If all constraints are met, record this solution
            rows = []
            for idx, house in enumerate(houses):
                row = [str(house), name_perm[idx], food_perm[idx]]
                rows.append(row)
            solutions.append(rows)

    # Assuming a unique solution exists
    if not solutions:
        raise ValueError("No solution found with given constraints.")
    if len(solutions) > 1:
        # Still output the first, but this indicates the constraints didn't lead to a unique solution
        rows = solutions[0]
    else:
        rows = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))