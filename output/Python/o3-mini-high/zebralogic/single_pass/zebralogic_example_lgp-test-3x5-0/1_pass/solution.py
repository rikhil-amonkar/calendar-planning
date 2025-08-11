#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    names = ["Peter", "Arnold", "Eric"]
    book_genres = ["science fiction", "mystery", "romance"]
    smoothies = ["watermelon", "desert", "cherry"]
    birthdays = ["april", "jan", "sept"]
    heights = ["average", "very short", "short"]

    # Iterate over all possible assignments via permutations.
    for name_perm in itertools.permutations(names):
        # Clue 7: Eric is in the first house.
        if name_perm[0] != "Eric":
            continue

        for smoothie_perm in itertools.permutations(smoothies):
            # Clue 9: The Watermelon smoothie lover is Eric.
            # Clue 7 already forces Eric in the first house, so his smoothie must be watermelon.
            if smoothie_perm[0] != "watermelon":
                continue
            # Clue 1: The person who likes Cherry smoothies is not in the second house.
            if smoothie_perm[1] == "cherry":
                continue

            for height_perm in itertools.permutations(heights):
                # Clue 8: The Watermelon smoothie lover is the person who is short.
                idx_watermelon = smoothie_perm.index("watermelon")
                if height_perm[idx_watermelon] != "short":
                    continue
                # Clue 6: The person who has an average height is the Desert smoothie lover.
                try:
                    idx_average = height_perm.index("average")
                except ValueError:
                    continue
                if smoothie_perm[idx_average] != "desert":
                    continue

                for birthday_perm in itertools.permutations(birthdays):
                    # Clue 3: The person whose birthday is in January is not in the first house.
                    if birthday_perm[0] == "jan":
                        continue

                    for book_perm in itertools.permutations(book_genres):
                        valid = True

                        # Clue 2: Arnold is the person who loves mystery books.
                        idx_arnold = name_perm.index("Arnold")
                        if book_perm[idx_arnold] != "mystery":
                            valid = False

                        # Clue 5: The person who loves mystery books is the person whose birthday is in September.
                        try:
                            idx_mystery = book_perm.index("mystery")
                        except ValueError:
                            valid = False
                        else:
                            if birthday_perm[idx_mystery] != "sept":
                                valid = False

                        # Clue 4: The person who is very short is the person who loves romance books.
                        for i in range(3):
                            if height_perm[i] == "very short" and book_perm[i] != "romance":
                                valid = False
                            if book_perm[i] == "romance" and height_perm[i] != "very short":
                                valid = False

                        if valid:
                            # Build the solution rows in house order.
                            solution_rows = []
                            for i in range(3):
                                solution_rows.append([
                                    str(i+1),
                                    name_perm[i],
                                    book_perm[i],
                                    smoothie_perm[i],
                                    birthday_perm[i],
                                    height_perm[i]
                                ])
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "favorite book genre", "favorite smoothie", "birthday month", "height"],
                                    "rows": solution_rows
                                }
                            }
                            print(json.dumps(solution))
                            sys.exit(0)

if __name__ == "__main__":
    main()