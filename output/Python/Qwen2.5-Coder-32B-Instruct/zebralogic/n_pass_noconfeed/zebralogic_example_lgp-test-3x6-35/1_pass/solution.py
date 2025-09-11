import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold", "Peter"]
    vacations = ["mountain", "city", "beach"]
    heights = ["very short", "average", "short"]
    flowers = ["carnations", "daffodils", "lilies"]
    hair_colors = ["brown", "black", "blonde"]
    educations = ["associate", "bachelor", "high school"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * 2 + \
                       list(itertools.permutations(vacations)) * 2 + \
                       list(itertools.permutations(heights)) * 2 + \
                       list(itertools.permutations(flowers)) * 2 + \
                       list(itertools.permutations(hair_colors)) * 2 + \
                       list(itertools.permutations(educations)) * 2

    # Iterate through all combinations of permutations
    for names_perm, vacations_perm, heights_perm, flowers_perm, hair_colors_perm, educations_perm in zip(
            all_permutations[::6], all_permutations[1::6], all_permutations[2::6],
            all_permutations[3::6], all_permutations[4::6], all_permutations[5::6]):

        # Create a list of dictionaries for each house
        houses = [
            {"House": "1", "Name": names_perm[0], "Vacation": vacations_perm[0],
             "Height": heights_perm[0], "Flower": flowers_perm[0],
             "HairColor": hair_colors_perm[0], "Education": educations_perm[0]},
            {"House": "2", "Name": names_perm[1], "Vacation": vacations_perm[1],
             "Height": heights_perm[1], "Flower": flowers_perm[1],
             "HairColor": hair_colors_perm[1], "Education": educations_perm[1]},
            {"House": "3", "Name": names_perm[2], "Vacation": vacations_perm[2],
             "Height": heights_perm[2], "Flower": flowers_perm[2],
             "HairColor": hair_colors_perm[2], "Education": educations_perm[2]}
        ]

        # Check all the clues
        if (houses[2]["Name"] == "Peter" and  # Clue 1
                houses[1]["Flower"] == "daffodils" and houses[1]["Name"] == "Arnold" and  # Clue 2
                houses[1]["Height"] != "very short" and  # Clue 3
                houses[0]["Vacation"] == "beach" and  # Clue 4
                houses[2]["Education"] == "high school" and  # Clue 5
                (houses[1]["Height"] == "short" or houses[2]["Height"] == "short") and  # Clue 6
                houses[2]["Flower"] == "lilies" and houses[2]["Name"] == "Eric" and  # Clue 7
                houses[2]["Education"] == "bachelor" and  # Clue 8
                (houses[1]["Vacation"] == "city" or houses[2]["Vacation"] == "city") and  # Clue 9
                houses[2]["HairColor"] == "blonde" and  # Clue 10
                houses[0]["Vacation"] == "beach" and houses[0]["HairColor"] == "brown"):  # Clue 11

            # If all clues are satisfied, return the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                    "rows": [
                        [house["House"], house["Name"], house["Vacation"], house["Height"],
                         house["Flower"], house["HairColor"], house["Education"]] for house in houses
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())