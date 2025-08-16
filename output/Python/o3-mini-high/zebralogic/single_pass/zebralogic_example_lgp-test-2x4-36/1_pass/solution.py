#!/usr/bin/env python3
import itertools
import json

def main():
    # Define the possible values for each attribute
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    birthdays = ["april", "sept"]
    animals = ["horse", "cat"]

    solution = None

    # Iterate over all possible assignments using permutations
    for name_perm in itertools.permutations(names):
        # Clue 1: Eric is in the first house.
        if name_perm[0] != "Eric":
            continue

        for genre_perm in itertools.permutations(book_genres):
            # Clue 3: The person who loves science fiction books is in the second house.
            if genre_perm[1] != "science fiction":
                continue

            for birthday_perm in itertools.permutations(birthdays):
                # Clue 2: Eric is the person whose birthday is in September.
                if birthday_perm[0] != "sept":
                    continue

                for animal_perm in itertools.permutations(animals):
                    valid = True
                    # Clue 4: The person who keeps horses is the person whose birthday is in September.
                    for i in range(len(houses)):
                        if birthday_perm[i] == "sept":
                            if animal_perm[i] != "horse":
                                valid = False
                                break
                        else:
                            if animal_perm[i] == "horse":
                                valid = False
                                break
                    if not valid:
                        continue

                    # If all constraints are satisfied, build the solution
                    solution = []
                    for i, house in enumerate(houses):
                        solution.append([str(house), name_perm[i], genre_perm[i], birthday_perm[i], animal_perm[i]])
                    break
                if solution is not None:
                    break
            if solution is not None:
                break
        if solution is not None:
            break

    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": solution
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()