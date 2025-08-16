import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    heights = ["short", "very short", "average"]

    # Generate all possible permutations for names and heights
    name_permutations = list(itertools.permutations(names))
    height_permutations = list(itertools.permutations(heights))

    # Iterate over all combinations of name and height permutations
    for name_order in name_permutations:
        for height_order in height_permutations:
            # Unpack the current permutation into individual variables
            name_house1, name_house2, name_house3 = name_order
            height_house1, height_house2, height_house3 = height_order

            # Check the constraints
            if (name_house1 != "Eric" and  # Constraint 1
                height_order.index("very short") < height_order.index("short") and  # Constraint 2
                name_order[height_order.index("very short")] == "Eric" and  # Constraint 3
                name_house1 != "Arnold"):  # Constraint 4

                # If all constraints are satisfied, construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Height"],
                        "rows": [
                            ["1", name_house1, height_house1],
                            ["2", name_house2, height_house2],
                            ["3", name_house3, height_house3]
                        ]
                    }
                }

                # Output the solution as a JSON string
                print(json.dumps(solution, indent=2))
                return

# Call the function to solve the puzzle
solve_puzzle()