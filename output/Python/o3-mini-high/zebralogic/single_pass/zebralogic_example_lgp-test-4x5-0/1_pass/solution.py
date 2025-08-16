#!/usr/bin/env python3
import itertools
import json

def valid(names, smoothies, cigars, heights, phones):
    # Constraint 1: The Dragonfruit smoothie lover is Eric.
    for i in range(4):
        if smoothies[i] == "dragonfruit" and names[i] != "Eric":
            return False
        if names[i] == "Eric" and smoothies[i] != "dragonfruit":
            return False

    # Constraint 2: The Dunhill smoker is the person who likes Cherry smoothies.
    for i in range(4):
        if cigars[i] == "dunhill" and smoothies[i] != "cherry":
            return False
        if smoothies[i] == "cherry" and cigars[i] != "dunhill":
            return False

    # Constraint 3: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
    adjacent = False
    for i in range(3):
        if phones[i] == "samsung galaxy s21" and phones[i+1] == "iphone 13":
            adjacent = True
            break
    if not adjacent:
        return False

    # Constraint 4: The Dunhill smoker is somewhere to the right of the person who is very short.
    try:
        index_very_short = heights.index("very short")
        index_dunhill = cigars.index("dunhill")
        if index_dunhill <= index_very_short:
            return False
    except ValueError:
        return False

    # Constraint 5: The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    try:
        index_desert = smoothies.index("desert")
        index_watermelon = smoothies.index("watermelon")
        if index_watermelon <= index_desert:
            return False
    except ValueError:
        return False

    # Constraint 6: The Prince smoker is the person who uses a OnePlus 9.
    for i in range(4):
        if cigars[i] == "prince" and phones[i] != "oneplus 9":
            return False
        if phones[i] == "oneplus 9" and cigars[i] != "prince":
            return False

    # Constraint 7: The person who is tall is in the third house.
    if heights[2] != "tall":
        return False

    # Constraint 8: The person who is very short is the person who uses an iPhone 13.
    for i in range(4):
        if heights[i] == "very short" and phones[i] != "iphone 13":
            return False
        if phones[i] == "iphone 13" and heights[i] != "very short":
            return False

    # Constraint 9: The person who smokes Blue Master is not in the first house.
    if cigars[0] == "blue master":
        return False

    # Constraint 10: The Dunhill smoker is the person who is short.
    for i in range(4):
        if cigars[i] == "dunhill" and heights[i] != "short":
            return False
        if heights[i] == "short" and cigars[i] != "dunhill":
            return False

    # Constraint 11: Peter is not in the third house.
    if names[2] == "Peter":
        return False

    # Constraint 12: Arnold is the person who uses a Google Pixel 6.
    for i in range(4):
        if names[i] == "Arnold" and phones[i] != "google pixel 6":
            return False
        if phones[i] == "google pixel 6" and names[i] != "Arnold":
            return False

    # Constraint 13: The Dragonfruit smoothie lover is the person partial to Pall Mall.
    for i in range(4):
        if smoothies[i] == "dragonfruit" and cigars[i] != "pall mall":
            return False
        if cigars[i] == "pall mall" and smoothies[i] != "dragonfruit":
            return False

    return True

def solve():
    names_all = ["Eric", "Peter", "Arnold", "Alice"]
    smoothies_all = ["dragonfruit", "cherry", "desert", "watermelon"]
    cigars_all = ["blue master", "pall mall", "dunhill", "prince"]
    heights_all = ["tall", "average", "short", "very short"]
    phones_all = ["google pixel 6", "samsung galaxy s21", "iphone 13", "oneplus 9"]

    for names in itertools.permutations(names_all):
        for smoothies in itertools.permutations(smoothies_all):
            for cigars in itertools.permutations(cigars_all):
                for heights in itertools.permutations(heights_all):
                    for phones in itertools.permutations(phones_all):
                        if valid(names, smoothies, cigars, heights, phones):
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
                                    "rows": []
                                }
                            }
                            for i in range(4):
                                house = str(i + 1)
                                solution["solution"]["rows"].append([house, names[i], smoothies[i], cigars[i], heights[i], phones[i]])
                            return solution
    return None

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result))