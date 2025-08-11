#!/usr/bin/env python3
import itertools
import json
import sys

def main():
    # Define all attribute lists
    names_all = ["Carol", "Bob", "Alice", "Arnold", "Eric", "Peter"]
    phones_all = ["samsung galaxy s21", "google pixel 6", "iphone 13", "huawei p50", "oneplus 9", "xiaomi mi 11"]
    # For phones, we will fix house5 and house6 as per clues.
    # House positions: indices 0..5 correspond to houses 1..6.
    nationalities_all = ["swede", "chinese", "norwegian", "dane", "german", "brit"]
    colors_all = ["blue", "red", "yellow", "green", "white", "purple"]

    # Fixed constraints based on clues:
    # Clue 8 & 10 & 15: house5 (index4) must use "samsung galaxy s21" (and that person is Bob),
    # and the phone to its right (house6, index5) must be "iphone 13".
    fixed_phone_index4 = "samsung galaxy s21"
    fixed_phone_index5 = "iphone 13"
    
    # For phones in houses 1-4 (indices 0-3), allowed options are the remaining phones.
    phones_options = [p for p in phones_all if p not in (fixed_phone_index4, fixed_phone_index5)]
    # That yields: ["google pixel 6", "huawei p50", "oneplus 9", "xiaomi mi 11"]

    # Begin search over permutations with constraints.
    for names in itertools.permutations(names_all):
        # Clue 1: Carol is not in the third house (index 2).
        if names[2] == "Carol":
            continue
        # Clue 10 & fixed assignment: Bob must be in the fifth house (index 4).
        if names[4] != "Bob":
            continue
        # Clue 14: Peter must be British and, by fixed order later, in the sixth house.
        if names[5] != "Peter":
            continue
        # Clue 4: Arnold is directly left of Alice.
        try:
            idx_arnold = names.index("Arnold")
            if idx_arnold == 5 or names[idx_arnold + 1] != "Alice":
                continue
        except ValueError:
            continue

        # Iterate over phone assignments (houses 0-3 come from phones_options; houses 5 and 6 fixed)
        for phone_perm in itertools.permutations(phones_options):
            phones = list(phone_perm) + [fixed_phone_index4, fixed_phone_index5]
            # Clue 7: The person who uses a Huawei P50 is not in the third house (index 2).
            if phones[2] == "huawei p50":
                continue

            # Iterate over nationalities
            for nat in itertools.permutations(nationalities_all):
                # Clue 14: Peter is British, so house6 (index 5) must be "brit".
                if nat[5] != "brit":
                    continue
                # Clue 2: There is one house between the Dane and the British person.
                # Since British is in house6 (index 5), Dane must be in house4 (index 3).
                if nat[3] != "dane":
                    continue
                # Clue 5: Alice is the German.
                idx_alice = names.index("Alice")
                if nat[idx_alice] != "german":
                    continue
                # Clue 17: The person who uses a Xiaomi Mi 11 is the Chinese.
                # Clue 6 & 16 (combined): The person who uses a OnePlus 9 loves purple and is Norwegian.
                valid_nat = True
                for i in range(6):
                    if phones[i] == "xiaomi mi 11" and nat[i] != "chinese":
                        valid_nat = False
                        break
                    if phones[i] == "oneplus 9" and nat[i] != "norwegian":
                        valid_nat = False
                        break
                if not valid_nat:
                    continue

                # Iterate over colors
                for colors in itertools.permutations(colors_all):
                    # Clue 3: Carol is the person whose favorite color is green.
                    idx_carol = names.index("Carol")
                    if colors[idx_carol] != "green":
                        continue
                    # Clue 13: The person who loves blue is Peter.
                    if colors[5] != "blue":
                        continue
                    # Clue 11: The Dane is the person who loves yellow.
                    # We already set the Dane in house4 (index 3).
                    if colors[3] != "yellow":
                        continue
                    # Clue 16: The Norwegian is the person who loves purple.
                    valid_color = True
                    for i in range(6):
                        if nat[i] == "norwegian" and colors[i] != "purple":
                            valid_color = False
                            break
                    if not valid_color:
                        continue
                    # Clue 6: The person who uses a OnePlus 9 is the person who loves purple.
                    for i in range(6):
                        if phones[i] == "oneplus 9" and colors[i] != "purple":
                            valid_color = False
                            break
                    if not valid_color:
                        continue
                    # Clue 9: The person who loves white is somewhere to the right of the person whose favorite color is red.
                    if colors.index("red") >= colors.index("white"):
                        continue

                    # Clue 12 is automatically satisfied by phone positions (S21 in house5 left of Peter in house6).
                    # Clue 15 is also satisfied by fixed phone positions (Samsung in house5, iPhone in house6).
                    # Clue 2 (one house between Dane and British) is satisfied by our fixed nationalities.
                    
                    # If all constraints pass, build the solution.
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Phone", "Nationality", "Color"],
                            "rows": []
                        }
                    }
                    for i in range(6):
                        solution["solution"]["rows"].append([
                            str(i + 1),
                            names[i],
                            phones[i],
                            nat[i],
                            colors[i]
                        ])
                    print(json.dumps(solution))
                    sys.exit(0)

if __name__ == '__main__':
    main()