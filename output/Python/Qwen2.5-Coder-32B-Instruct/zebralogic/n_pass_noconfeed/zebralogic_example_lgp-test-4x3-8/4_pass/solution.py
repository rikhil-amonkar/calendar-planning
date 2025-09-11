import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold", "Peter", "Alice"]
    hair_colors = ["blonde", "black", "brown", "red"]
    music_genres = ["pop", "jazz", "rock", "classical"]

    # Generate all possible permutations for the categories
    name_permutations = list(itertools.permutations(names))
    hair_permutations = list(itertools.permutations(hair_colors))
    music_permutations = list(itertools.permutations(music_genres))

    # Iterate over all possible combinations of permutations
    for names_order in name_permutations:
        for hair_order in hair_permutations:
            for music_order in music_permutations:
                # Unpack the permutations into individual lists for each house
                name1, name2, name3, name4 = names_order
                hair1, hair2, hair3, hair4 = hair_order
                music1, music2, music3, music4 = music_order

                # Check the constraints
                if (name1 == "Eric" and hair1 == "red" and
                    music1 == "classical" and
                    music2 == "jazz" and
                    name2 == "Arnold" and
                    hair3 != "brown" and
                    music3 != "pop" and
                    hair2 == "blonde" and
                    names_order.index("Peter") > names_order.index("Arnold")):

                    # Construct the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HairColor", "MusicGenre"],
                            "rows": [
                                ["1", name1, hair1, music1],
                                ["2", name2, hair2, music2],
                                ["3", name3, hair3, music3],
                                ["4", name4, hair4, music4]
                            ]
                        }
                    }

                    # Output the solution as JSON
                    print(json.dumps(solution, indent=2))
                    return

    # If no solution is found, print a message
    print("No solution found")

# Run the solver
solve_puzzle()