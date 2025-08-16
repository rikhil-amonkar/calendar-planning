import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold", "Peter", "Alice"]
    hair_colors = ["blonde", "black", "brown", "red"]
    music_genres = ["pop", "jazz", "rock", "classical"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names))
    permutations_hair = list(itertools.permutations(hair_colors))
    permutations_music = list(itertools.permutations(music_genres))

    # Iterate over all possible combinations of permutations
    for perm_name in permutations:
        for perm_hair in permutations_hair:
            for perm_music in permutations_music:
                # Unpack the permutations for easier access
                name1, name2, name3, name4 = perm_name
                hair1, hair2, hair3, hair4 = perm_hair
                music1, music2, music3, music4 = perm_music

                # Apply the clues to check if the current combination is valid
                if (name1 == "Eric" and hair1 == "red" and
                    music1 == "classical" and
                    music2 == "jazz" and
                    name2 == "Arnold" and music2 == "rock" and
                    hair3 != "brown" and
                    music3 != "pop" and
                    name3 != "Arnold" and
                    name4 != "Arnold" and
                    perm_name.index("Peter") > perm_name.index("Arnold")):

                    # If all clues are satisfied, construct the solution
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

# Call the function to solve the puzzle
solve_puzzle()