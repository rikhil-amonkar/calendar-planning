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
                            # Create a dictionary to store the current combination
                            current_solution = {
                                "1": {"Name": names_perm[0], "Flower": flowers_perm[0],
                                      "Hair Color": hair_colors_perm[0], "Sport": sports_perm[0],
                                      "House Style": house_styles_perm[0], "Pet": pets_perm[0]},
                                "2": {"Name": names_perm[1], "Flower": flowers_perm[1],
                                      "Hair Color": hair_colors_perm[1], "Sport": sports_perm[1],
                                      "House Style": house_styles_perm[1], "Pet": pets_perm[1]},
                                "3": {"Name": names_perm[2], "Flower": flowers_perm[2],
                                      "Hair Color": hair_colors_perm[2], "Sport": sports_perm[2],
                                      "House Style": house_styles_perm[2], "Pet": pets_perm[2]}
                            }

                            # Check all the clues
                            if (current_solution["3"]["Pet"] == "cat" and current_solution["3"]["Sport"] == "soccer" and
                                current_solution["2"]["Hair Color"] == "blonde" and
                                current_solution["2"]["Flower"] == "daffodils" and
                                current_solution["3"]["Name"] == "Peter" and
                                current_solution["2"]["Pet"] == "dog" and
                                current_solution["1"]["Flower"] == "carnations" and
                                current_solution["1"]["Hair Color"] == "blonde" and
                                current_solution["3"]["Sport"] == "soccer" and
                                current_solution["3"]["House Style"] == "colonial" and
                                current_solution["1"]["Name"] == "Arnold" and
                                current_solution["1"]["Hair Color"] != "black" and
                                current_solution["2"]["Name"] != "Arnold" and
                                current_solution["2"]["Hair Color"] != "black" and
                                current_solution["3"]["Name"] != "Arnold" and
                                current_solution["3"]["Hair Color"] == "black"):
                                
                                # If all clues are satisfied, format the solution as JSON
                                solution_json = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Hair Color", "Sport", "House Style", "Pet"],
                                        "rows": [
                                            ["1", current_solution["1"]["Name"], current_solution["1"]["Flower"],
                                             current_solution["1"]["Hair Color"], current_solution["1"]["Sport"],
                                             current_solution["1"]["House Style"], current_solution["1"]["Pet"]],
                                            ["2", current_solution["2"]["Name"], current_solution["2"]["Flower"],
                                             current_solution["2"]["Hair Color"], current_solution["2"]["Sport"],
                                             current_solution["2"]["House Style"], current_solution["2"]["Pet"]],
                                            ["3", current_solution["3"]["Name"], current_solution["3"]["Flower"],
                                             current_solution["3"]["Hair Color"], current_solution["3"]["Sport"],
                                             current_solution["3"]["House Style"], current_solution["3"]["Pet"]]
                                        ]
                                    }
                                }
                                print(json.dumps(solution_json, indent=2))
                                return

# Run the function to solve the puzzle
solve_puzzle()