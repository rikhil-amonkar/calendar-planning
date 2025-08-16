#!/usr/bin/env python3
import json
import itertools

def solve_puzzle():
    names = ["Arnold", "Eric"]
    book_genres = ["science fiction", "mystery"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]

    # There are 2 houses: index 0 represents House 1 and index 1 represents House 2.
    for name_perm in itertools.permutations(names):
        for book_perm in itertools.permutations(book_genres):
            # Clue 5: The person who loves mystery books is in the first house.
            if book_perm[0] != "mystery":
                continue
            for vac_perm in itertools.permutations(vacations):
                for animal_perm in itertools.permutations(animals):
                    # Clue 4: The cat lover is not in the second house.
                    if animal_perm[1] == "cat":
                        continue
                    for music_perm in itertools.permutations(music_genres):
                        valid = True
                        # Check constraints for each house
                        for i in range(2):
                            # Clue 1: The person who loves beach vacations is Eric.
                            if vac_perm[i] == "beach" and name_perm[i] != "Eric":
                                valid = False
                                break
                            if name_perm[i] == "Eric" and vac_perm[i] != "beach":
                                valid = False
                                break
                            # Clue 2: The person who loves pop music is the person who loves beach vacations.
                            if music_perm[i] == "pop" and vac_perm[i] != "beach":
                                valid = False
                                break
                            if vac_perm[i] == "beach" and music_perm[i] != "pop":
                                valid = False
                                break
                            # Clue 3: The person who loves rock music is the person who loves mystery books.
                            if music_perm[i] == "rock" and book_perm[i] != "mystery":
                                valid = False
                                break
                            if book_perm[i] == "mystery" and music_perm[i] != "rock":
                                valid = False
                                break
                        if valid:
                            # Build the solution rows in order for houses 1 and 2.
                            rows = [
                                ["1", name_perm[0], book_perm[0], vac_perm[0], animal_perm[0], music_perm[0]],
                                ["2", name_perm[1], book_perm[1], vac_perm[1], animal_perm[1], music_perm[1]]
                            ]
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                                    "rows": rows
                                }
                            }
                            return result
    return None

def main():
    solution = solve_puzzle()
    # If no solution is found, output an empty rows list.
    if solution is None:
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                "rows": []
            }
        }
    print(json.dumps(solution))

if __name__ == "__main__":
    main()