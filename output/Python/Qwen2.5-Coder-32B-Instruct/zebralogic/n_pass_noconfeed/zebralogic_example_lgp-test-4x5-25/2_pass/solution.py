import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Peter", "Eric", "Alice"]
    house_styles = ["craftsman", "colonial", "victorian", "ranch"]
    hair_colors = ["red", "blonde", "black", "brown"]
    children = ["Bella", "Fred", "Meredith", "Samantha"]
    book_genres = ["mystery", "fantasy", "romance", "science fiction"]

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(4)))

    # Check each permutation against the clues
    for name_order in all_permutations:
        for house_style_order in all_permutations:
            for hair_color_order in all_permutations:
                for children_order in all_permutations:
                    for book_genre_order in all_permutations:
                        # Create a dictionary to store the current permutation
                        current_solution = {
                            "House": [str(i + 1) for i in range(4)],
                            "Name": [names[name_order[i]] for i in range(4)],
                            "HouseStyle": [house_styles[house_style_order[i]] for i in range(4)],
                            "HairColor": [hair_colors[hair_color_order[i]] for i in range(4)],
                            "Children": [children[children_order[i]] for i in range(4)],
                            "BookGenre": [book_genres[book_genre_order[i]] for i in range(4)]
                        }

                        # Apply the clues to check if this permutation is valid
                        if (current_solution["HouseStyle"][2] == "craftsman" and  # Clue 1
                            current_solution["Name"][current_solution["BookGenre"].index("romance")] == "Alice" and  # Clue 2
                            current_solution["HairColor"][3] == "brown" and  # Clue 3
                            current_solution["Children"][3] == "Samantha" and  # Clue 4
                            current_solution["House"].index(str(current_solution["HairColor"].index("red") + 1)) < current_solution["House"].index(str(current_solution["HouseStyle"].index("ranch") + 1)) and  # Clue 5
                            current_solution["Children"][current_solution["Name"].index("Peter")] == "Bella" and  # Clue 6
                            current_solution["HairColor"][current_solution["Name"].index("Arnold")] == "red" and  # Clue 7
                            current_solution["HouseStyle"][current_solution["Name"].index("Alice")] == "colonial" and  # Clue 8
                            current_solution["HairColor"][1] == "black" and  # Clue 9
                            current_solution["BookGenre"][current_solution["Name"].index("Peter")] == "fantasy" and  # Clue 10
                            current_solution["Children"][current_solution["Name"].index("Arnold")] == "Meredith" and  # Clue 11
                            current_solution["Name"][current_solution["HairColor"].index("black")] == "Eric" and  # Clue 12
                            current_solution["BookGenre"][current_solution["Name"].index("Arnold")] == "science fiction"):  # Clue 13

                            # If all clues are satisfied, format the solution as required
                            solution_rows = [
                                [current_solution["House"][i], current_solution["Name"][i], current_solution["HouseStyle"][i],
                                 current_solution["HairColor"][i], current_solution["Children"][i], current_solution["BookGenre"][i]]
                                for i in range(4)
                            ]

                            solution_dict = {
                                "solution": {
                                    "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                                    "rows": solution_rows
                                }
                            }

                            # Print the solution as JSON
                            print(json.dumps(solution_dict, indent=2))
                            return

# Run the function to solve the puzzle
solve_puzzle()