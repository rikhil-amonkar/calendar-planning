import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric", "Peter"]
    flowers = ["carnations", "lilies", "daffodils"]
    hair_colors = ["black", "brown", "blonde"]
    sports = ["soccer", "basketball", "tennis"]
    house_styles = ["colonial", "ranch", "victorian"]
    pets = ["fish", "dog", "cat"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(flowers)) + \
                       list(itertools.permutations(hair_colors)) + \
                       list(itertools.permutations(sports)) + \
                       list(itertools.permutations(house_styles)) + \
                       list(itertools.permutations(pets))

    # Iterate over all possible combinations of permutations
    for names_perm in all_permutations[:6]:
        for flowers_perm in all_permutations[6:12]:
            for hair_colors_perm in all_permutations[12:18]:
                for sports_perm in all_permutations[18:24]:
                    for house_styles_perm in all_permutations[24:30]:
                        for pets_perm in all_permutations[30:36]:
                            # Create a dictionary to store the current permutation
                            current_solution = {
                                "1": {"Name": names_perm[0], "Flower": flowers_perm[0], "HairColor": hair_colors_perm[0],
                                      "FavoriteSport": sports_perm[0], "HouseStyle": house_styles_perm[0], "Pet": pets_perm[0]},
                                "2": {"Name": names_perm[1], "Flower": flowers_perm[1], "HairColor": hair_colors_perm[1],
                                      "FavoriteSport": sports_perm[1], "HouseStyle": house_styles_perm[1], "Pet": pets_perm[1]},
                                "3": {"Name": names_perm[2], "Flower": flowers_perm[2], "HairColor": hair_colors_perm[2],
                                      "FavoriteSport": sports_perm[2], "HouseStyle": house_styles_perm[2], "Pet": pets_perm[2]}
                            }

                            # Check all the clues
                            if (current_solution["3"]["Pet"] == "cat" and current_solution["3"]["FavoriteSport"] == "soccer" and
                                current_solution["2"]["HairColor"] == "blonde" and
                                current_solution["2"]["Flower"] == "daffodils" and
                                current_solution["3"]["Name"] == "Peter" and
                                current_solution["2"]["Pet"] == "dog" and
                                current_solution["2"]["FavoriteSport"] == "basketball" and
                                current_solution["1"]["Flower"] == "carnations" and
                                current_solution["2"]["HairColor"] == "blonde" and
                                current_solution["1"]["Name"] == "Arnold" and
                                current_solution["3"]["HouseStyle"] == "colonial" and
                                names.index(current_solution["1"]["Name"]) < names.index(current_solution["2"]["Name"]) and
                                names.index(current_solution["2"]["Name"]) < names.index(current_solution["3"]["Name"]) and
                                hair_colors.index(current_solution["1"]["HairColor"]) < hair_colors.index(current_solution["3"]["HairColor"])):

                                # If all clues are satisfied, format the solution as required
                                solution_rows = []
                                for house_number in ["1", "2", "3"]:
                                    row = [house_number,
                                           current_solution[house_number]["Name"],
                                           current_solution[house_number]["Flower"],
                                           current_solution[house_number]["HairColor"],
                                           current_solution[house_number]["FavoriteSport"],
                                           current_solution[house_number]["HouseStyle"],
                                           current_solution[house_number]["Pet"]]
                                    solution_rows.append(row)

                                final_solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "HairColor", "FavoriteSport", "HouseStyle", "Pet"],
                                        "rows": solution_rows
                                    }
                                }

                                # Output the solution as JSON
                                print(json.dumps(final_solution))
                                return

# Run the solver
solve_puzzle()