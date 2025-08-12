import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    favorite_sports = ["basketball", "soccer"]
    favorite_smoothies = ["desert", "cherry"]

    # Generate all possible permutations for the houses
    all_permutations = list(itertools.permutations(names))
    all_permutations *= list(itertools.permutations(hair_colors))
    all_permutations *= list(itertools.permutations(favorite_sports))
    all_permutations *= list(itertools.permutations(favorite_smoothies))

    # Define the constraints
    def is_valid_solution(solution):
        # Unpack the solution
        (name1, name2), (hair_color1, hair_color2), (sport1, sport2), (smoothie1, smoothie2) = solution

        # Constraint 1: The Desert smoothie lover is Arnold.
        if smoothie1 == "desert" and name1 != "Arnold":
            return False
        if smoothie2 == "desert" and name2 != "Arnold":
            return False

        # Constraint 2: The person who has brown hair is the person who loves basketball.
        if hair_color1 == "brown" and sport1 != "basketball":
            return False
        if hair_color2 == "brown" and sport2 != "basketball":
            return False

        # Constraint 3: Arnold is somewhere to the left of the person who has black hair.
        if name1 == "Arnold" and hair_color2 != "black":
            return False
        if name2 == "Arnold" and hair_color1 != "black":
            return False

        return True

    # Find the valid solution
    for permutation in itertools.product(all_permutations, repeat=4):
        if is_valid_solution(permutation):
            (name1, name2), (hair_color1, hair_color2), (sport1, sport2), (smoothie1, smoothie2) = permutation
            solution = {
                "solution": {
                    "header": ["House", "Name", "Hair Color", "Favorite Sport", "Favorite Smoothie"],
                    "rows": [
                        ["1", name1, hair_color1, sport1, smoothie1],
                        ["2", name2, hair_color2, sport2, smoothie2]
                    ]
                }
            }
            print(json.dumps(solution, indent=2))
            return

solve_puzzle()