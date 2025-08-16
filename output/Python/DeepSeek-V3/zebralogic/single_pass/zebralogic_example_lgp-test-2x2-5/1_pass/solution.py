import json
from itertools import permutations

def solve_puzzle():
    # Define the possible attributes
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    
    # Generate all possible permutations of house styles for the 2 houses
    for styles in permutations(house_styles, 2):
        # Check clue 1: Victorian is left of colonial
        if styles.index("victorian") < styles.index("colonial"):
            # Check clue 2: Eric is in the first house
            # Try both name permutations (Eric must be in house 1)
            for name_order in permutations(names, 2):
                if name_order[0] == "Eric":
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HouseStyle"],
                            "rows": [
                                ["1", name_order[0], styles[0]],
                                ["2", name_order[1], styles[1]]
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

print(solve_puzzle())