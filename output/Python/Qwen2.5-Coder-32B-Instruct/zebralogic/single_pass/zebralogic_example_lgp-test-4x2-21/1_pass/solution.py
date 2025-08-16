import itertools
import json

def solve_puzzle():
    # Define the possible values for each characteristic
    names = ["Eric", "Arnold", "Alice", "Peter"]
    house_styles = ["craftsman", "colonial", "ranch", "victorian"]
    
    # Generate all possible permutations for the houses
    all_permutations = list(itertools.permutations(names))
    house_style_permutations = list(itertools.permutations(house_styles))
    
    # Define the constraints
    def is_valid_solution(names_order, house_styles_order):
        # Constraint 1: Alice is in the second house.
        if names_order[1] != "Alice":
            return False
        
        # Constraint 5: The person in a Craftsman-style house is Alice.
        if house_styles_order[names_order.index("Alice")] != "craftsman":
            return False
        
        # Constraint 2: The person residing in a Victorian house is directly left of Peter.
        if house_styles_order.index("victorian") + 1 >= len(house_styles_order) or names_order[house_styles_order.index("victorian") + 1] != "Peter":
            return False
        
        # Constraint 3: Peter is somewhere to the right of the person in a ranch-style home.
        if house_styles_order.index("ranch") > house_styles_order.index("victorian"):
            return False
        
        # Constraint 4: Arnold is somewhere to the right of the person in a Craftsman-style house.
        if names_order.index("Arnold") < names_order.index("Alice"):
            return False
        
        return True
    
    # Find the valid solution
    for names_order in all_permutations:
        for house_styles_order in house_style_permutations:
            if is_valid_solution(names_order, house_styles_order):
                # Format the solution as required
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HouseStyle"],
                        "rows": [
                            [str(i + 1), names_order[i], house_styles_order[i]] for i in range(4)
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Print the solution
print(solve_puzzle())