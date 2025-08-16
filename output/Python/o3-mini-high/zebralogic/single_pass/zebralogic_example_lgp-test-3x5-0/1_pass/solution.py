#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    # Define the possible values for each attribute
    names = ["Peter", "Arnold", "Eric"]
    book_genres = ["science fiction", "mystery", "romance"]
    smoothies = ["watermelon", "desert", "cherry"]
    birthdays = ["april", "jan", "sept"]
    heights = ["average", "very short", "short"]
    
    solution_found = False

    # Iterate over all permutations and apply constraints
    for name_perm in itertools.permutations(names):
        # Constraint: Eric must be in the first house.
        if name_perm[0] != "Eric":
            continue
        for birthday_perm in itertools.permutations(birthdays):
            # Constraint: The person whose birthday is in January is not in the first house.
            if birthday_perm[0] == "jan":
                continue
            for genre_perm in itertools.permutations(book_genres):
                for smoothie_perm in itertools.permutations(smoothies):
                    # Constraint: The person who likes Cherry smoothies is not in the second house.
                    if smoothie_perm[1] == "cherry":
                        continue
                    for height_perm in itertools.permutations(heights):
                        valid = True
                        # Check constraints for each house (houses are indexed 0, 1, 2 corresponding to houses 1, 2, 3)
                        for i in range(3):
                            # Clue 9 & 7: Eric is in the first house and he is the Watermelon smoothie lover.
                            if name_perm[i] == "Eric" and smoothie_perm[i] != "watermelon":
                                valid = False
                                break
                            # Clue 9 (reverse): The Watermelon smoothie lover is Eric.
                            if smoothie_perm[i] == "watermelon" and name_perm[i] != "Eric":
                                valid = False
                                break
                            # Clue 2: Arnold is the person who loves mystery books.
                            if name_perm[i] == "Arnold" and genre_perm[i] != "mystery":
                                valid = False
                                break
                            # Clue 5: The person who loves mystery books is the person whose birthday is in September.
                            # Enforce both directions.
                            if genre_perm[i] == "mystery" and birthday_perm[i] != "sept":
                                valid = False
                                break
                            if birthday_perm[i] == "sept" and genre_perm[i] != "mystery":
                                valid = False
                                break
                            # Clue 6: The person who has an average height is the Desert smoothie lover.
                            if smoothie_perm[i] == "desert" and height_perm[i] != "average":
                                valid = False
                                break
                            if height_perm[i] == "average" and smoothie_perm[i] != "desert":
                                valid = False
                                break
                            # Clue 4: The person who is very short is the person who loves romance books.
                            if height_perm[i] == "very short" and genre_perm[i] != "romance":
                                valid = False
                                break
                            if genre_perm[i] == "romance" and height_perm[i] != "very short":
                                valid = False
                                break
                        if valid:
                            # Build the candidate solution as a list of rows.
                            rows = []
                            for i in range(3):
                                # House numbers are 1-indexed.
                                row = [str(i + 1), name_perm[i], genre_perm[i], smoothie_perm[i], birthday_perm[i], height_perm[i]]
                                rows.append(row)
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                                    "rows": rows
                                }
                            }
                            print(json.dumps(result))
                            sys.exit(0)
                            
    # If no solution is found, output an empty rows list.
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
            "rows": []
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()