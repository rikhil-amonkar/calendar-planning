import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Eric", "Alice", "Arnold"]
    educations = ["bachelor", "high school", "associate", "master"]
    music_genres = ["jazz", "rock", "pop", "classical"]
    colors = ["green", "red", "yellow", "white"]
    flowers = ["lilies", "carnations", "daffodils", "roses"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) + \
                       list(itertools.permutations(educations)) + \
                       list(itertools.permutations(music_genres)) + \
                       list(itertools.permutations(colors)) + \
                       list(itertools.permutations(flowers))

    # Iterate through all combinations of permutations
    for names_perm in all_permutations[::len(names)]:
        for educations_perm in all_permutations[len(names)::len(educations)]:
            for music_genres_perm in all_permutations[2*len(educations)::len(music_genres)]:
                for colors_perm in all_permutations[3*len(music_genres)::len(colors)]:
                    for flowers_perm in all_permutations[4*len(colors)::len(flowers)]:
                        # Create a dictionary to store the current permutation
                        current_solution = {
                            "1": {"name": names_perm[0], "education": educations_perm[0], "music_genre": music_genres_perm[0], "color": colors_perm[0], "flower": flowers_perm[0]},
                            "2": {"name": names_perm[1], "education": educations_perm[1], "music_genre": music_genres_perm[1], "color": colors_perm[1], "flower": flowers_perm[1]},
                            "3": {"name": names_perm[2], "education": educations_perm[2], "music_genre": music_genres_perm[2], "color": colors_perm[2], "flower": flowers_perm[2]},
                            "4": {"name": names_perm[3], "education": educations_perm[3], "music_genre": music_genres_perm[3], "color": colors_perm[3], "flower": flowers_perm[3]}
                        }

                        # Check all the clues
                        if (current_solution["1"]["education"] == "bachelor" and current_solution["1"]["flower"] == "daffodils") and \
                           (current_solution["2"]["flower"] != "carnations") and \
                           (current_solution["3"]["name"] == "Alice" and current_solution["3"]["education"] == "master") and \
                           (current_solution["3"]["music_genre"] == "classical") and \
                           (current_solution["2"]["name"] != "Eric") and \
                           (current_solution["3"]["name"] != "Arnold") and \
                           (current_solution["2"]["color"] == "yellow" and current_solution["3"]["flower"] == "roses") and \
                           (current_solution["2"]["music_genre"] == "pop") and \
                           (current_solution["4"]["education"] != "associate") and \
                           (current_solution["4"]["flower"] != "carnations") and \
                           (current_solution["1"]["color"] == "red" and current_solution["2"]["color"] == "white") and \
                           (current_solution["1"]["music_genre"] == "rock") and \
                           (current_solution["1"]["color"] == "yellow") and \
                           (current_solution["1"]["flower"] == "daffodils"):
                            # If all clues are satisfied, format the solution as required
                            solution_rows = []
                            for house_number in ["1", "2", "3", "4"]:
                                row = [house_number,
                                       current_solution[house_number]["name"],
                                       current_solution[house_number]["education"],
                                       current_solution[house_number]["music_genre"],
                                       current_solution[house_number]["color"],
                                       current_solution[house_number]["flower"]]
                                solution_rows.append(row)

                            solution_dict = {
                                "solution": {
                                    "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
                                    "rows": solution_rows
                                }
                            }

                            # Print the solution as JSON
                            print(json.dumps(solution_dict, indent=2))
                            return

# Call the function to solve the puzzle
solve_puzzle()