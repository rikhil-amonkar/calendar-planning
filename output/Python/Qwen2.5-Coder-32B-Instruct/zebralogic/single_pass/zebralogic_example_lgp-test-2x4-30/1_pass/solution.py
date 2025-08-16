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
    for names_perm in itertools.permutations(names):
        for hair_colors_perm in itertools.permutations(hair_colors):
            for favorite_sports_perm in itertools.permutations(favorite_sports):
                for smoothies_perm in itertools.permutations(smoothies):
                    # Unpack the permutations
                    name1, name2 = names_perm
                    hair_color1, hair_color2 = hair_colors_perm
                    favorite_sport1, favorite_sport2 = favorite_sports_perm
                    smoothie1, smoothie2 = smoothies_perm

                    # Apply the clues
                    if (smoothie1 == "desert" and name1 == "Arnold" and
                        hair_color2 == "brown" and favorite_sport2 == "basketball" and
                        names.index(name1) < names.index(name2) if name2 in names else True and
                        hair_color1 == "black" if name1 == "Eric" else True and
                        hair_color2 == "black" if name2 == "Arnold" else True):

                        # Construct the solution
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
                        print(json.dumps(solution))
                        return

# Run the function to solve the puzzle
solve_puzzle()