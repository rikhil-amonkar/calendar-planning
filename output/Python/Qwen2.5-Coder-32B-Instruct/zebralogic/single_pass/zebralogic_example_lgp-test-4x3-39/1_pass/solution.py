import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    houses = [1, 2, 3, 4]
    names = ["Eric", "Alice", "Peter", "Arnold"]
    hair_colors = ["blonde", "black", "red", "brown"]
    favorite_sports = ["swimming", "soccer", "basketball", "tennis"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(hair_colors)) * \
                   list(itertools.permutations(favorite_sports))

    # Check each permutation against the clues
    for names_perm, hair_colors_perm, favorite_sports_perm in zip(permutations[::3], permutations[1::3], permutations[2::3]):
        # Unpack the permutations
        name_to_house = dict(zip(houses, names_perm))
        hair_color_to_house = dict(zip(houses, hair_colors_perm))
        favorite_sport_to_house = dict(zip(houses, favorite_sports_perm))

        # Apply the clues
        if (favorite_sport_to_house[2] != "soccer" and
            name_to_house[eric_house := hair_color_to_house.index("blonde") + 1] == "Eric" and
            eric_house > basketball_house := favorite_sports_perm.index("basketball") + 1 and
            hair_color_to_house[tennis_house := favorite_sport_to_house.index("tennis") + 1] == "black" and
            arnold_house := names_perm.index("Arnold") + 1 < red_hair_house := hair_color_to_house.index("red") + 1 and
            name_to_house[swimming_house := favorite_sport_to_house.index("swimming") + 1] == "Alice" and
            red_hair_house == tennis_house - 1):
            # If all conditions are met, construct the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "HairColor", "FavoriteSport"],
                    "rows": []
                }
            }
            for house in houses:
                solution["solution"]["rows"].append([
                    str(house),
                    name_to_house[house],
                    hair_color_to_house[house],
                    favorite_sport_to_house[house]
                ])
            return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())