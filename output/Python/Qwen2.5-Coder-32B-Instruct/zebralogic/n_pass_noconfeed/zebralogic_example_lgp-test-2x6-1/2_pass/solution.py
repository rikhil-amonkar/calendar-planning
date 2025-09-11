import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    sports = ["basketball", "soccer"]
    hair_colors = ["brown", "black"]
    heights = ["very short", "short"]
    smoothies = ["desert", "cherry"]
    flowers = ["daffodils", "carnations"]

    # Generate all possible permutations for each category
    name_perms = list(itertools.permutations(names))
    sport_perms = list(itertools.permutations(sports))
    hair_color_perms = list(itertools.permutations(hair_colors))
    height_perms = list(itertools.permutations(heights))
    smoothie_perms = list(itertools.permutations(smoothies))
    flower_perms = list(itertools.permutations(flowers))

    # Generate all possible combinations of permutations for two houses
    all_combinations = itertools.product(
        name_perms, sport_perms, hair_color_perms, height_perms, smoothie_perms, flower_perms
    )

    # Iterate over all possible combinations of permutations for two houses
    for comb in itertools.product(all_combinations, repeat=2):
        house1, house2 = comb

        # Unpack the permutations into dictionaries for easier access
        house1_dict = {
            "Name": house1[0][0],
            "FavoriteSport": house1[1][0],
            "HairColor": house1[2][0],
            "Height": house1[3][0],
            "Smoothie": house1[4][0],
            "Flower": house1[5][0]
        }
        house2_dict = {
            "Name": house2[0][0],
            "FavoriteSport": house2[1][0],
            "HairColor": house2[2][0],
            "Height": house2[3][0],
            "Smoothie": house2[4][0],
            "Flower": house2[5][0]
        }

        # Check all the clues
        if (house1_dict["FavoriteSport"] == "soccer" or house2_dict["FavoriteSport"] != "soccer") and \
           (house1_dict["Smoothie"] == "desert" and house2_dict["Height"] == "very short") and \
           (house2_dict["Height"] == "very short" and house2_dict["HairColor"] == "brown") and \
           (house1_dict["Flower"] == "carnations" and house1_dict["Smoothie"] == "desert") and \
           (house1_dict["Name"] == "Eric" or house2_dict["Name"] == "Eric") and \
           ((house1_dict["Name"] == "Eric" and house2_dict["HairColor"] == "brown") or
            (house2_dict["Name"] == "Eric" and house1_dict["HairColor"] == "brown")):

            # Construct the solution in the required format
            solution = {
                "solution": {
                    "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
                    "rows": [
                        ["1", house1_dict["Name"], house1_dict["FavoriteSport"], house1_dict["HairColor"],
                         house1_dict["Height"], house1_dict["Smoothie"], house1_dict["Flower"]],
                        ["2", house2_dict["Name"], house2_dict["FavoriteSport"], house2_dict["HairColor"],
                         house2_dict["Height"], house2_dict["Smoothie"], house2_dict["Flower"]]
                    ]
                }
            }

            # Output the solution as JSON
            print(json.dumps(solution, indent=2))
            return

# Run the function to solve the puzzle
solve_puzzle()