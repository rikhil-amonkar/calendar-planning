import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    favorite_sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]

    # Generate all possible permutations for each category
    name_permutations = list(itertools.permutations(names))
    hair_color_permutations = list(itertools.permutations(hair_colors))
    favorite_sport_permutations = list(itertools.permutations(favorite_sports))
    smoothie_permutations = list(itertools.permutations(smoothies))

    # Use itertools.product to get the Cartesian product of all permutations
    all_combinations = itertools.product(name_permutations, 
                                         hair_color_permutations, 
                                         favorite_sport_permutations, 
                                         smoothie_permutations)

    # Check each combination against the clues
    for comb in all_combinations:
        name1, name2 = comb[0]
        hair_color1, hair_color2 = comb[1]
        favorite_sport1, favorite_sport2 = comb[2]
        smoothie1, smoothie2 = comb[3]

        # Apply the clues
        if (smoothie1 == "desert" and name1 == "Arnold" and
            hair_color2 == "black" and
            (hair_color1 == "brown" and favorite_sport1 == "basketball" or
             hair_color2 == "brown" and favorite_sport2 == "basketball")):

            # Construct the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
                    "rows": [
                        ["1", name1, hair_color1, favorite_sport1, smoothie1],
                        ["2", name2, hair_color2, favorite_sport2, smoothie2]
                    ]
                }
            }

            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            return

# Run the function to solve the puzzle
solve_puzzle()