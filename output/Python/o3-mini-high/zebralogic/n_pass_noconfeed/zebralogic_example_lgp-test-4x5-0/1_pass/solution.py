#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    names_list = ["Eric", "Peter", "Arnold", "Alice"]
    smoothies_list = ["dragonfruit", "cherry", "desert", "watermelon"]
    cigars_list = ["blue master", "pall mall", "dunhill", "prince"]
    heights_list = ["tall", "average", "short", "very short"]
    phones_list = ["google pixel 6", "samsung galaxy s21", "iphone 13", "oneplus 9"]

    # The houses are numbered 1 to 4 (index 0 .. 3)
    # Iterate over all permutations, using early constraint checks
    for heights in itertools.permutations(heights_list):
        # Constraint 7: The person who is tall is in the third house (house number 3 -> index 2)
        if heights[2] != "tall":
            continue

        for phones in itertools.permutations(phones_list):
            # Constraint 3: The Samsung Galaxy S21 is directly left of the iPhone 13.
            found_pair = False
            for i in range(3):  # check indices 0-2 with neighbor at i+1
                if phones[i] == "samsung galaxy s21" and phones[i+1] == "iphone 13":
                    found_pair = True
                    break
            if not found_pair:
                continue

            # Constraint 8: The person who is very short uses the iPhone 13 and vice versa.
            valid_iphone = True
            for i in range(4):
                if phones[i] == "iphone 13" and heights[i] != "very short":
                    valid_iphone = False
                    break
                if heights[i] == "very short" and phones[i] != "iphone 13":
                    valid_iphone = False
                    break
            if not valid_iphone:
                continue

            for names in itertools.permutations(names_list):
                # Constraint 11: Peter is not in the third house (index 2)
                if names[2] == "Peter":
                    continue

                for smoothies in itertools.permutations(smoothies_list):
                    # Constraint 1 & 13: The Dragonfruit smoothie lover is Eric and he smokes Pall Mall.
                    valid_dragon = True
                    for i in range(4):
                        if smoothies[i] == "dragonfruit" and names[i] != "Eric":
                            valid_dragon = False
                            break
                        if names[i] == "Eric" and smoothies[i] != "dragonfruit":
                            valid_dragon = False
                            break
                    if not valid_dragon:
                        continue

                    # Constraint 5: The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
                    try:
                        desert_index = smoothies.index("desert")
                        water_index = smoothies.index("watermelon")
                        if desert_index >= water_index:
                            continue
                    except ValueError:
                        continue

                    for cigars in itertools.permutations(cigars_list):
                        # Constraint 9: The Blue Master smoker is not in the first house.
                        if cigars[0] == "blue master":
                            continue

                        # Constraint 2 & 10: The Dunhill smoker is the person who likes Cherry smoothies
                        # and is the person who is short.
                        valid_dunhill = True
                        for i in range(4):
                            if cigars[i] == "dunhill":
                                if smoothies[i] != "cherry" or heights[i] != "short":
                                    valid_dunhill = False
                                    break
                            if smoothies[i] == "cherry" and cigars[i] != "dunhill":
                                valid_dunhill = False
                                break
                        if not valid_dunhill:
                            continue

                        # Constraint 6: The Prince smoker is the person who uses a OnePlus 9.
                        valid_prince = True
                        for i in range(4):
                            if cigars[i] == "prince" and phones[i] != "oneplus 9":
                                valid_prince = False
                                break
                            if phones[i] == "oneplus 9" and cigars[i] != "prince":
                                valid_prince = False
                                break
                        if not valid_prince:
                            continue

                        # Constraint 4: The Dunhill smoker is somewhere to the right of the person who is very short.
                        try:
                            pos_very_short = heights.index("very short")
                            pos_dunhill = cigars.index("dunhill")
                            if pos_dunhill <= pos_very_short:
                                continue
                        except ValueError:
                            continue

                        # Constraint 13 (reiterated): The Dragonfruit smoothie lover is the person partial to Pall Mall.
                        valid_dragon_pall = True
                        for i in range(4):
                            if smoothies[i] == "dragonfruit" and cigars[i] != "pall mall":
                                valid_dragon_pall = False
                                break
                            if cigars[i] == "pall mall" and smoothies[i] != "dragonfruit":
                                valid_dragon_pall = False
                                break
                        if not valid_dragon_pall:
                            continue

                        # Constraint 12: Arnold is the person who uses a Google Pixel 6.
                        valid_arnold = True
                        for i in range(4):
                            if phones[i] == "google pixel 6" and names[i] != "Arnold":
                                valid_arnold = False
                                break
                            if names[i] == "Arnold" and phones[i] != "google pixel 6":
                                valid_arnold = False
                                break
                        if not valid_arnold:
                            continue

                        # If all constraints pass, we have found the solution.
                        solution_rows = []
                        for i in range(4):
                            house_number = str(i + 1)
                            row = [
                                house_number,
                                names[i],
                                smoothies[i],
                                cigars[i],
                                heights[i],
                                phones[i]
                            ]
                            solution_rows.append(row)
                        result = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                                "rows": solution_rows
                            }
                        }
                        print(json.dumps(result, indent=2))
                        sys.exit(0)

if __name__ == "__main__":
    main()