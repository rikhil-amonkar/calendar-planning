import json

def solve_puzzle():
    # Define the possible options for each attribute
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]

    # Initialize possible assignments
    from itertools import product
    solutions = []

    # Generate all possible combinations
    for name_assignment in product(names, repeat=2):
        if len(set(name_assignment)) != 2:
            continue  # Names must be unique
        for food_assignment in product(foods, repeat=2):
            if len(set(food_assignment)) != 2:
                continue  # Foods must be unique

            # Check constraints
            # Constraint 1: pizza lover is in house 2
            if food_assignment[1] != "pizza":
                continue
            # Constraint 2: Arnold is not in house 1
            if name_assignment[0] == "Arnold":
                continue

            # If all constraints are satisfied, add to solutions
            solution = {
                1: {"Name": name_assignment[0], "Food": food_assignment[0]},
                2: {"Name": name_assignment[1], "Food": food_assignment[1]},
            }
            solutions.append(solution)

    # Prepare the output
    output = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": []
        }
    }

    for house in sorted(solutions[0].keys()):
        row = [str(house)]
        row.append(solutions[0][house]["Name"])
        row.append(solutions[0][house]["Food"])
        output["solution"]["rows"].append(row)

    return json.dumps(output)

if __name__ == "__main__":
    print(solve_puzzle())