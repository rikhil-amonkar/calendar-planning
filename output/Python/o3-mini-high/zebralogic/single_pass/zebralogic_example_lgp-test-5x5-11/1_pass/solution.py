#!/usr/bin/env python3
import itertools
import json

def main():
    names_list = ["Peter", "Arnold", "Eric", "Bob", "Alice"]
    heights_list = ["average", "very tall", "very short", "short", "tall"]
    cigars_list = ["prince", "dunhill", "blends", "pall mall", "blue master"]
    smoothies_list = ["lime", "cherry", "dragonfruit", "watermelon", "desert"]
    phones_list = ["oneplus 9", "samsung galaxy s21", "iphone 13", "huawei p50", "google pixel 6"]

    # Iterate over all assignments for "names"
    for names in itertools.permutations(names_list):
        # House positions: indices 0 to 4 (1-indexed houses 1-5)
        # Clue 8: Bob is not in the fourth house (index 3)
        if names[3] == "Bob":
            continue

        # Clue 2: There is one house between Eric and Alice
        try:
            pos_Eric = names.index("Eric")
            pos_Alice = names.index("Alice")
        except ValueError:
            continue
        if abs(pos_Eric - pos_Alice) != 2:
            continue

        # Clue 14 (and Clue 11): The Dragonfruit smoothie lover is Bob and there are two houses between the person who is very tall and this person.
        try:
            pos_Bob = names.index("Bob")
        except ValueError:
            continue
        if abs(pos_Eric - pos_Bob) != 3:
            continue

        # Iterate over heights assignments
        for heights in itertools.permutations(heights_list):
            # Clue 6: Eric is very tall.
            if heights[pos_Eric] != "very tall":
                continue
            # Clue 5 and Clue 10: The person who has an average height is the Dunhill smoker and Bob is Dunhill.
            if heights[pos_Bob] != "average":
                continue
            # Clue 17: Arnold and the person who is very short are next to each other.
            try:
                pos_very_short = heights.index("very short")
            except ValueError:
                continue
            pos_arnold = names.index("Arnold")
            if abs(pos_arnold - pos_very_short) != 1:
                continue

            # Iterate over cigars assignments
            for cigars in itertools.permutations(cigars_list):
                valid = True
                # Clue 3: The person who is short is the person who smokes blends.
                for i in range(5):
                    if heights[i] == "short" and cigars[i] != "blends":
                        valid = False
                        break
                    if cigars[i] == "blends" and heights[i] != "short":
                        valid = False
                        break
                if not valid:
                    continue
                
                # Clue 5: The person who has an average height is the Dunhill smoker.
                for i in range(5):
                    if heights[i] == "average" and cigars[i] != "dunhill":
                        valid = False
                        break
                if not valid:
                    continue

                # Clue 10: Bob is the Dunhill smoker.
                if cigars[pos_Bob] != "dunhill":
                    continue

                # Iterate over smoothies assignments
                for smoothies in itertools.permutations(smoothies_list):
                    # Clue 11: The Dragonfruit smoothie lover is Bob.
                    if smoothies[pos_Bob] != "dragonfruit":
                        continue

                    # Clue 9: Eric is directly left of the person who likes Cherry smoothies.
                    if pos_Eric == 4 or smoothies[pos_Eric + 1] != "cherry":
                        continue

                    valid_sm = True
                    # Clue 1: The Prince smoker is the Desert smoothie lover.
                    for i in range(5):
                        if cigars[i] == "prince" and smoothies[i] != "desert":
                            valid_sm = False
                            break
                        if smoothies[i] == "desert" and cigars[i] != "prince":
                            valid_sm = False
                            break
                    if not valid_sm:
                        continue

                    # Clue 16: The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
                    try:
                        pos_desert = smoothies.index("desert")
                        pos_lime = smoothies.index("lime")
                    except ValueError:
                        continue
                    if not (pos_desert < pos_lime):
                        continue

                    # Iterate over phones assignments
                    for phones in itertools.permutations(phones_list):
                        valid_ph = True
                        # Clue 15: The person who uses an iPhone 13 is Eric.
                        if phones[pos_Eric] != "iphone 13":
                            continue

                        # Clue 4: The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
                        if pos_Eric == 4 or cigars[pos_Eric + 1] != "blue master":
                            continue

                        # Clue 7: Arnold is directly left of the person who uses a Huawei P50.
                        pos_arnold = names.index("Arnold")
                        if pos_arnold == 4 or phones[pos_arnold + 1] != "huawei p50":
                            continue

                        # Clue 12: The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
                        pos_iphone = pos_Eric  # since Eric has iphone 13.
                        neighbor_found = False
                        if pos_iphone > 0 and phones[pos_iphone - 1] == "oneplus 9":
                            neighbor_found = True
                        if pos_iphone < 4 and phones[pos_iphone + 1] == "oneplus 9":
                            neighbor_found = True
                        if not neighbor_found:
                            continue

                        # Clue 13: The person who uses a Samsung Galaxy S21 is the person who is short.
                        for i in range(5):
                            if heights[i] == "short" and phones[i] != "samsung galaxy s21":
                                valid_ph = False
                                break
                            if phones[i] == "samsung galaxy s21" and heights[i] != "short":
                                valid_ph = False
                                break
                        if not valid_ph:
                            continue

                        # All constraints satisfied; build solution.
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
                                "rows": []
                            }
                        }
                        for i in range(5):
                            row = [str(i+1), names[i], heights[i], cigars[i], smoothies[i], phones[i]]
                            solution["solution"]["rows"].append(row)
                        print(json.dumps(solution))
                        return

if __name__ == '__main__':
    main()