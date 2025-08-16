#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    names = ["Arnold", "Eric", "Peter"]
    music_genres = ["pop", "rock", "classical"]
    children = ["Fred", "Meredith", "Bella"]
    book_genres = ["mystery", "romance", "science fiction"]

    # We have 3 houses; we'll represent each house as a dict.
    # House numbers: 1, 2, 3 (we keep 0-indexed internally)
    for names_perm in itertools.permutations(names):
        # Clue 2: Peter is in the first house.
        if names_perm[0] != "Peter":
            continue
        for music_perm in itertools.permutations(music_genres):
            for children_perm in itertools.permutations(children):
                for book_perm in itertools.permutations(book_genres):
                    houses = []
                    for i in range(3):
                        houses.append({
                            "Name": names_perm[i],
                            "MusicGenre": music_perm[i],
                            "Children": children_perm[i],
                            "BookGenre": book_perm[i]
                        })
                    
                    valid = True

                    # Constraint 1:
                    # The house whose child is Fred must be immediately left of the house that loves mystery books.
                    # That means: for any house with BookGenre "mystery", the house immediately to its left must have Children "Fred".
                    for i in range(3):
                        if houses[i]["BookGenre"] == "mystery":
                            if i == 0 or houses[i-1]["Children"] != "Fred":
                                valid = False
                                break
                    if not valid:
                        continue

                    # Constraint 3:
                    # The person who loves mystery books is the person who loves classical music.
                    for i in range(3):
                        if houses[i]["BookGenre"] == "mystery":
                            if houses[i]["MusicGenre"] != "classical":
                                valid = False
                                break
                    if not valid:
                        continue

                    # Constraint 4:
                    # The person whose child is named Meredith loves science fiction books.
                    for i in range(3):
                        if houses[i]["Children"] == "Meredith":
                            if houses[i]["BookGenre"] != "science fiction":
                                valid = False
                                break
                    if not valid:
                        continue

                    # Constraint 5:
                    # Eric is the person who loves mystery books.
                    for i in range(3):
                        if houses[i]["BookGenre"] == "mystery":
                            if houses[i]["Name"] != "Eric":
                                valid = False
                                break
                    if not valid:
                        continue

                    # Constraint 6:
                    # The person who loves rock music is somewhere to the right of the person who loves romance books.
                    rock_index = None
                    romance_index = None
                    for i in range(3):
                        if houses[i]["MusicGenre"] == "rock":
                            rock_index = i
                        if houses[i]["BookGenre"] == "romance":
                            romance_index = i
                    if rock_index is None or romance_index is None or rock_index <= romance_index:
                        valid = False
                    if not valid:
                        continue

                    # If we have a valid assignment, output the solution in the required JSON format.
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                            "rows": [
                                [str(1), houses[0]["Name"], houses[0]["MusicGenre"], houses[0]["Children"], houses[0]["BookGenre"]],
                                [str(2), houses[1]["Name"], houses[1]["MusicGenre"], houses[1]["Children"], houses[1]["BookGenre"]],
                                [str(3), houses[2]["Name"], houses[2]["MusicGenre"], houses[2]["Children"], houses[2]["BookGenre"]]
                            ]
                        }
                    }
                    print(json.dumps(solution))
                    sys.exit(0)

if __name__ == "__main__":
    main()