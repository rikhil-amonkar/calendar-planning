import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Arnold", "Eric", "Alice"]
    flowers = ["daffodils", "carnations", "roses", "lilies"]
    heights = ["very short", "short", "tall", "average"]
    mothers = ["Janelle", "Kailyn", "Holly", "Aniya"]
    occupations = ["engineer", "doctor", "teacher", "artist"]
    sports = ["swimming", "basketball", "tennis", "soccer"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(range(4)))

    # Check all combinations of permutations
    for name_perm in all_permutations:
        for flower_perm in all_permutations:
            for height_perm in all_permutations:
                for mother_perm in all_permutations:
                    for occupation_perm in all_permutations:
                        for sport_perm in all_permutations:
                            # Create a dictionary to store the current permutation
                            current_solution = {
                                "House 1": {"Name": names[name_perm[0]], "Flower": flowers[flower_perm[0]],
                                            "Height": heights[height_perm[0]], "Mother": mothers[mother_perm[0]],
                                            "Occupation": occupations[occupation_perm[0]], "FavoriteSport": sports[sport_perm[0]]},
                                "House 2": {"Name": names[name_perm[1]], "Flower": flowers[flower_perm[1]],
                                            "Height": heights[height_perm[1]], "Mother": mothers[mother_perm[1]],
                                            "Occupation": occupations[occupation_perm[1]], "FavoriteSport": sports[sport_perm[1]]},
                                "House 3": {"Name": names[name_perm[2]], "Flower": flowers[flower_perm[2]],
                                            "Height": heights[height_perm[2]], "Mother": mothers[mother_perm[2]],
                                            "Occupation": occupations[occupation_perm[2]], "FavoriteSport": sports[sport_perm[2]]},
                                "House 4": {"Name": names[name_perm[3]], "Flower": flowers[flower_perm[3]],
                                            "Height": heights[height_perm[3]], "Mother": mothers[mother_perm[3]],
                                            "Occupation": occupations[occupation_perm[3]], "FavoriteSport": sports[sport_perm[3]]}
                            }

                            # Apply the clues to check if the current permutation is valid
                            if (current_solution["House 1"]["FavoriteSport"] == "swimming" and
                                current_solution["House 1"]["Flower"] == "roses" and
                                current_solution["House 2"]["Flower"] == "roses" and
                                current_solution["House 2"]["Name"] == "Eric" and
                                current_solution[f"House {name_perm.index(names.index('Arnold')) + 1}"]["Height"] == "tall" and
                                flower_perm.index(flowers.index("daffodils")) > occupation_perm.index(occupations.index("engineer")) and
                                current_solution[f"House {sport_perm.index(sports.index('soccer')) + 1}"]["Height"] == "short" and
                                current_solution["House 1"]["Occupation"] == "teacher" and
                                current_solution[f"House {mother_perm.index(mothers.index('Janelle')) + 1}"]["Flower"] == "carnations" and
                                current_solution[f"House {sport_perm.index(sports.index('basketball')) + 1}"]["Height"] == "average" and
                                name_perm.index(names.index("Arnold")) != 2 and
                                mother_perm.index(mothers.index("Holly")) > height_perm.index(heights.index("average")) and
                                current_solution[f"House {name_perm.index(names.index('Peter')) + 1}"]["Occupation"] == "doctor" and
                                current_solution[f"House {mother_perm.index(mothers.index('Aniya')) + 1}"]["Name"] == "Alice" and
                                current_solution[f"House {name_perm.index(names.index('Arnold')) + 1}"]["Flower"] == "lilies"):
                                
                                # Format the solution as required
                                solution_rows = []
                                for i in range(1, 5):
                                    house_info = current_solution[f"House {i}"]
                                    solution_rows.append([
                                        str(i),
                                        house_info["Name"],
                                        house_info["Flower"],
                                        house_info["Height"],
                                        house_info["Mother"],
                                        house_info["Occupation"],
                                        house_info["FavoriteSport"]
                                    ])

                                solution_dict = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                                        "rows": solution_rows
                                    }
                                }

                                # Output the solution as JSON
                                print(json.dumps(solution_dict, indent=2))
                                return

# Run the function to solve the puzzle
solve_puzzle()