import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Arnold", "Alice", "Peter"]
    house_styles = ["craftsman", "colonial", "ranch", "victorian"]

    # Generate all possible permutations for names and house styles
    permutations = list(itertools.permutations(names))
    style_permutations = list(itertools.permutations(house_styles))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(name_order, style_order):
        # Clue 1: Alice is in the second house.
        if name_order[1] != "Alice":
            return False
        # Clue 5: The person in a Craftsman-style house is Alice.
        if style_order[name_order.index("Alice")] != "craftsman":
            return False
        # Find Peter's position
        peter_pos = name_order.index("Peter")
        # Clue 2: The person residing in a Victorian house is directly left of Peter.
        if peter_pos == 0 or style_order[peter_pos - 1] != "victorian":
            return False
        # Clue 3: Peter is somewhere to the right of the person in a ranch-style home.
        ranch_pos = style_order.index("ranch")
        if peter_pos <= ranch_pos:
            return False
        # Clue 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
        craftsman_pos = style_order.index("craftsman")
        arnold_pos = name_order.index("Arnold")
        if arnold_pos <= craftsman_pos:
            return False
        return True

    # Iterate over all permutations to find the valid solution
    for name_order in permutations:
        for style_order in style_permutations:
            if is_valid_solution(name_order, style_order):
                # Construct the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Style"],
                        "rows": []
                    }
                }
                for i in range(4):
                    solution["solution"]["rows"].append([
                        str(i + 1),
                        name_order[i],
                        style_order[i]
                    ])
                return json.dumps(solution, indent=2)

# Output the solution
print(solve_puzzle())