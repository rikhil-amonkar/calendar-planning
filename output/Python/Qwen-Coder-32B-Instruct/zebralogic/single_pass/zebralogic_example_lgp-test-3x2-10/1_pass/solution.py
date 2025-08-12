import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Arnold", "Peter"]
    heights = ["short", "very short", "average"]

    # Generate all possible permutations for the attributes
    all_permutations = list(itertools.permutations(names)) * len(list(itertools.permutations(heights)))
    height_permutations = list(itertools.permutations(heights))

    # Initialize a variable to store the solution
    solution = None

    # Iterate over all possible combinations of permutations
    for name_order in itertools.permutations(names):
        for height_order in itertools.permutations(heights):
            # Unpack the permutations into individual variables
            name1, name2, name3 = name_order
            height1, height2, height3 = height_order

            # Check the constraints
            if (name1 != "Eric" and
                name1 != "Arnold" and
                name2 != "Arnold" and
                height_order.index("very short") < height_order.index("short") and
                height1 == "very short"):
                
                # If all constraints are satisfied, store the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Height"],
                        "rows": [
                            ["1", name1, height1],
                            ["2", name2, height2],
                            ["3", name3, height3]
                        ]
                    }
                }
                break
        if solution:
            break

    # Output the solution as a JSON-formatted string
    print(json.dumps(solution, indent=2))

# Call the function to solve the puzzle
solve_puzzle()