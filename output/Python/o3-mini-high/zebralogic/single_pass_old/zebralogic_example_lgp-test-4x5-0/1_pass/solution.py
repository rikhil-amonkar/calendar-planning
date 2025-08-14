#!/usr/bin/env python3
import itertools
import json

names = ["Eric", "Peter", "Arnold", "Alice"]
smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
cigars  = ["blue master", "pall mall", "dunhill", "prince"]
heights = ["tall", "average", "short", "very short"]
phones  = ["google pixel 6", "samsung galaxy s21", "iphone 13", "oneplus 9"]

solution_found = None

for ns in itertools.permutations(names):
    # Clue 11: Peter is not in the third house (house 3 is index 2)
    if ns[2] == "Peter":
        continue
    for sm in itertools.permutations(smoothies):
        # Clue 1: The Dragonfruit smoothie lover is Eric.
        if sm[ns.index("Eric")] != "dragonfruit":
            continue
        # Clue 5: The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
        if sm.index("watermelon") <= sm.index("desert"):
            continue
        for cig in itertools.permutations(cigars):
            # Clue 13: The Dragonfruit smoothie lover is the person partial to Pall Mall.
            if cig[sm.index("dragonfruit")] != "pall mall":
                continue
            # Clue 2: The Dunhill smoker is the person who likes Cherry smoothies.
            if sm.index("cherry") != cig.index("dunhill"):
                continue
            # Clue 9: The person who smokes Blue Master is not in the first house.
            if cig[0] == "blue master":
                continue
            for ht in itertools.permutations(heights):
                # Clue 7: The person who is tall is in the third house.
                if ht[2] != "tall":
                    continue
                # Clue 10: The Dunhill smoker is the person who is short.
                if ht.index("short") != cig.index("dunhill"):
                    continue
                for ph in itertools.permutations(phones):
                    # Clue 3: The person who uses a Samsung Galaxy S21 is directly left of the person who uses an iPhone 13.
                    try:
                        idx_samsung = ph.index("samsung galaxy s21")
                    except ValueError:
                        continue
                    if idx_samsung == 3 or ph[idx_samsung + 1] != "iphone 13":
                        continue
                    # Clue 8: The person who is very short is the person who uses an iPhone 13.
                    if ht.index("very short") != ph.index("iphone 13"):
                        continue
                    # Clue 4: The Dunhill smoker is somewhere to the right of the person who is very short.
                    if cig.index("dunhill") <= ht.index("very short"):
                        continue
                    # Clue 6: The Prince smoker is the person who uses a OnePlus 9.
                    if cig.index("prince") != ph.index("oneplus 9"):
                        continue
                    # Clue 12: Arnold is the person who uses a Google Pixel 6.
                    if ns.index("Arnold") != ph.index("google pixel 6"):
                        continue

                    # All constraints satisfied; construct the solution.
                    solution_found = []
                    for i in range(4):
                        # House numbers are 1-indexed.
                        solution_found.append([str(i+1), ns[i], sm[i], cig[i], ht[i], ph[i]])
                    break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

if solution_found:
    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "Phone"],
            "rows": solution_found
        }
    }
    print(json.dumps(output))
else:
    print(json.dumps({"solution": { "header": [], "rows": [] }}))