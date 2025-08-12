import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Peter", "Arnold", "Alice", "Eric"]
    colors = ["yellow", "green", "red", "white"]

    # Generate all possible permutations for names and colors
    all_permutations = list(itertools.permutations(names)) * list(itertools.permutations(colors))

    # Define the constraints
    def is_valid_solution(names_order, colors_order):
        # Constraint 1: The person whose favorite color is green is in the third house.
        if colors_order[2] != "green":
            return False
        # Constraint 2: Peter is in the first house.
        if names_order[0] != "Peter":
            return False
        # Constraint 3: There is one house between the person whose favorite color is red and the person who loves yellow.
        if abs(colors_order.index("red") - colors_order.index("yellow")) != 2:
            return False
        # Constraint 4: Arnold is directly left of Eric.
        if names_order.index("Arnold") + 1 != names_order.index("Eric"):
            return False
        # Constraint 5: Eric is the person who loves yellow.
        if names_order[colors_order.index("yellow")] != "Eric":
            return False
        return True

    # Find the valid solution
    for names_order, colors_order in zip(all_permutations[::len(colors)], all_permutations[len(names)::len(names)]):
        if is_valid_solution(names_order, colors_order):
            solution = {
                "solution": {
                    "header": ["House", "Name", "Color"],
                    "rows": [
                        [str(i+1), names_order[i], colors_order[i]] for i in range(4)
                    ]
                }
            }
            print(json.dumps(solution, indent=2))
            return

# Run the solver
solve_puzzle()