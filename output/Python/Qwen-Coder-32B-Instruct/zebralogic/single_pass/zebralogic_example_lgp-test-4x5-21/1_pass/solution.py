import itertools
import json

def solve_puzzle():
    # Define the attributes and their possible values
    names = ["Eric", "Alice", "Peter", "Arnold"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    sports = ["soccer", "tennis", "basketball", "swimming"]
    cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    flowers = ["daffodils", "roses", "lilies", "carnations"]

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(smoothies)) + \
                       list(itertools.permutations(sports)) + \
                       list(itertools.permutations(cars)) + \
                       list(itertools.permutations(flowers))

    # Iterate over all possible combinations of permutations
    for names_perm in all_permutations[:24]:
        for smoothies_perm in all_permutations[24:48]:
            for sports_perm in all_permutations[48:72]:
                for cars_perm in all_permutations[72:96]:
                    for flowers_perm in all_permutations[96:120]:
                        # Check all constraints
                        if (cars_perm[smoothies_perm.index("dragonfruit")] == "tesla model 3" and
                            flowers_perm[smoothies_perm.index("dragonfruit")] == "roses" and
                            names_perm[smoothies_perm.index("dragonfruit")] == "Peter" and
                            cars_perm[smoothies_perm.index("desert")] == "toyota camry" and
                            sports_perm[0] == "tennis" and
                            abs(cars_perm.index("toyota camry") - sports_perm.index("basketball")) == 1 and
                            names_perm[sports_perm.index("basketball")] == "Arnold" and
                            cars_perm[flowers_perm.index("daffodils")] == "honda civic" and
                            names_perm[flowers_perm.index("roses")] == "Eric" and
                            smoothies_perm[0] != "watermelon" and
                            cars_perm.index("honda civic") > smoothies_perm.index("desert") and
                            flowers_perm[sports_perm.index("basketball")] == "lilies" and
                            abs(sports_perm.index("tennis") - sports_perm.index("soccer")) == 1):
                            
                            # If all constraints are satisfied, construct the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "Sport", "Car", "Flower"],
                                    "rows": [
                                        ["1", names_perm[0], smoothies_perm[0], sports_perm[0], cars_perm[0], flowers_perm[0]],
                                        ["2", names_perm[1], smoothies_perm[1], sports_perm[1], cars_perm[1], flowers_perm[1]],
                                        ["3", names_perm[2], smoothies_perm[2], sports_perm[2], cars_perm[2], flowers_perm[2]],
                                        ["4", names_perm[3], smoothies_perm[3], sports_perm[3], cars_perm[3], flowers_perm[3]]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())