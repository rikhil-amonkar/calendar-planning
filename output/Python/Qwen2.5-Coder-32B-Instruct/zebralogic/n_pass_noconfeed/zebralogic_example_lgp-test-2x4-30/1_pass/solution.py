import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    favorite_sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]

    # Generate all possible permutations for the two houses
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(hair_colors)) * \
                       list(itertools.permutations(favorite_sports)) * \
                       list(itertools.permutations(smoothies))

    # Check each permutation against the clues
    for perm in all_permutations:
        name1, name2 = perm[0], perm[1]
        hair_color1, hair_color2 = perm[2], perm[3]
        favorite_sport1, favorite_sport2 = perm[4], perm[5]
        smoothie1, smoothie2 = perm[6], perm[7]

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