import json
import itertools

def solve_zebra_puzzle():
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]

    solutions = []
    # Generate all permutations for the names and foods across the houses.
    for name_perm in itertools.permutations(names):
        for food_perm in itertools.permutations(foods):
            # Assign values to each house in order
            assignment = {
                1: {"Name": name_perm[0], "Food": food_perm[0]},
                2: {"Name": name_perm[1], "Food": food_perm[1]}
            }
            # Constraint 1: The pizza lover lives in the second house.
            if assignment[2]["Food"] != "pizza":
                continue
            # Constraint 2: Arnold is not in the first house.
            if assignment[1]["Name"] == "Arnold":
                continue
            solutions.append(assignment)

    # Assuming there is a unique valid solution
    if solutions:
        valid_assignment = solutions[0]
        # Prepare the output in the required JSON structure.
        result = {
            "solution": {
                "header": ["House", "Name", "Food"],
                "rows": [
                    [str(h), valid_assignment[h]["Name"], valid_assignment[h]["Food"]]
                    for h in sorted(valid_assignment.keys())
                ]
            }
        }
    else:
        result = {"solution": {"header": ["House", "Name", "Food"], "rows": []}}

    return result

if __name__ == "__main__":
    solution = solve_zebra_puzzle()
    print(json.dumps(solution))