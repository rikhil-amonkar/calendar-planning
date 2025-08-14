#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Arnold", "Eric"]
    book_genres = ["science fiction", "mystery"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]

    solution = None

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
                        for i in range(2):
                            # Clue 1: The person who loves beach vacations is Eric.
                            if vac_perm[i] == "beach" and name_perm[i] != "Eric":
                                valid = False
                                break
                            # Clue 2: The person who loves pop music is the person who loves beach vacations.
                            if vac_perm[i] == "beach" and music_perm[i] != "pop":
                                valid = False
                                break
                            if music_perm[i] == "pop" and vac_perm[i] != "beach":
                                valid = False
                                break
                            # Clue 3: The person who loves rock music is the person who loves mystery books.
                            if book_perm[i] == "mystery" and music_perm[i] != "rock":
                                valid = False
                                break
                            if music_perm[i] == "rock" and book_perm[i] != "mystery":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Build solution rows for houses 1 and 2.
                        houses = []
                        for i in range(2):
                            house_info = [str(i+1), name_perm[i], book_perm[i], vac_perm[i], animal_perm[i], music_perm[i]]
                            houses.append(house_info)
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Book Genre", "Vacation", "Animal", "Music Genre"],
                                "rows": houses
                            }
                        }
                        break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break
        if solution:
            break

    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()