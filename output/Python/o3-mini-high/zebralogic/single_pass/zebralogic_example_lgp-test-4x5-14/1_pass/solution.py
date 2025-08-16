#!/usr/bin/env python3
from itertools import permutations
import json

def main():
    names_list = ["Peter", "Alice", "Eric", "Arnold"]
    mothers_list = ["Janelle", "Holly", "Aniya", "Kailyn"]
    smoothies_list = ["watermelon", "dragonfruit", "desert", "cherry"]
    heights_list = ["tall", "average", "short", "very short"]
    educations_list = ["high school", "associate", "master", "bachelor"]

    # We'll use 0-indexed houses: index 0 = House 1, index 1 = House 2, etc.
    # Many clues force fixed attributes for House 3 (index 2):
    #   - Name must be "Alice"
    #   - Mother must be "Janelle"
    #   - Height must be "tall"
    solution_found = None

    for names_perm in permutations(names_list):
        # Clue12 forces: the person who is tall is Alice.
        # And by later constraints the only "Alice" must be in the house where height is tall.
        # We also enforce that House 3 is Alice.
        if names_perm[2] != "Alice":
            continue

        for mothers_perm in permutations(mothers_list):
            # Clue1: The person whose mother's name is Janelle is in the third house.
            if mothers_perm[2] != "Janelle":
                continue

            for heights_perm in permutations(heights_list):
                # Clue12 & Clue9: The person who is tall is Alice, and tall <-> Janelle.
                if heights_perm[2] != "tall":
                    continue
                valid_tall_mother = True
                for i in range(4):
                    # If a house is tall it must have mother Janelle.
                    if heights_perm[i] == "tall" and mothers_perm[i] != "Janelle":
                        valid_tall_mother = False
                        break
                    # If the mother is Janelle then the height must be tall.
                    if mothers_perm[i] == "Janelle" and heights_perm[i] != "tall":
                        valid_tall_mother = False
                        break
                if not valid_tall_mother:
                    continue

                for smoothies_perm in permutations(smoothies_list):
                    # Clue3: The Desert smoothie lover is not in the first house.
                    if smoothies_perm[0] == "desert":
                        continue

                    for educations_perm in permutations(educations_list):
                        # Clue6: The person with a high school diploma is not in the third house.
                        if educations_perm[2] == "high school":
                            continue

                        # Clue2: The Desert smoothie lover is the person with a master's degree.
                        valid_desert_master = True
                        for i in range(4):
                            if smoothies_perm[i] == "desert" and educations_perm[i] != "master":
                                valid_desert_master = False
                                break
                            if educations_perm[i] == "master" and smoothies_perm[i] != "desert":
                                valid_desert_master = False
                                break
                        if not valid_desert_master:
                            continue

                        # Clue7: The person whose mother's name is Kailyn is the person with an associate's degree.
                        valid_kailyn_associate = True
                        for i in range(4):
                            if mothers_perm[i] == "Kailyn" and educations_perm[i] != "associate":
                                valid_kailyn_associate = False
                                break
                            if educations_perm[i] == "associate" and mothers_perm[i] != "Kailyn":
                                valid_kailyn_associate = False
                                break
                        if not valid_kailyn_associate:
                            continue

                        # Clue8: The person who likes Cherry smoothies is the person whose mother's name is Aniya.
                        valid_cherry_aniya = True
                        for i in range(4):
                            if smoothies_perm[i] == "cherry" and mothers_perm[i] != "Aniya":
                                valid_cherry_aniya = False
                                break
                            if mothers_perm[i] == "Aniya" and smoothies_perm[i] != "cherry":
                                valid_cherry_aniya = False
                                break
                        if not valid_cherry_aniya:
                            continue

                        # Clue4: The person who is very short is somewhere to the left of the person with a high school diploma.
                        try:
                            idx_very_short = heights_perm.index("very short")
                            idx_high_school = educations_perm.index("high school")
                        except ValueError:
                            continue
                        if not (idx_very_short < idx_high_school):
                            continue

                        # Clue5: Eric and the person who likes Cherry smoothies are next to each other.
                        idx_eric = names_perm.index("Eric")
                        try:
                            idx_cherry = smoothies_perm.index("cherry")
                        except ValueError:
                            continue
                        if abs(idx_eric - idx_cherry) != 1:
                            continue

                        # Clue10: Arnold is somewhere to the right of the person who has an average height.
                        idx_average = heights_perm.index("average")
                        idx_arnold = names_perm.index("Arnold")
                        if not (idx_average < idx_arnold):
                            continue

                        # Clue11: The Dragonfruit smoothie lover is directly left of the person who is short.
                        try:
                            idx_dragon = smoothies_perm.index("dragonfruit")
                        except ValueError:
                            continue
                        if idx_dragon == 3:
                            continue
                        if heights_perm[idx_dragon + 1] != "short":
                            continue

                        # Clue12 (bidirectional): The person who is tall is Alice.
                        # Given uniqueness, ensure the house with "tall" in heights is the same as the one with "Alice" in names.
                        if names_perm.index("Alice") != heights_perm.index("tall"):
                            continue

                        # All constraints satisfied, record the solution.
                        solution_found = [
                            [ "1", names_perm[0], mothers_perm[0], smoothies_perm[0], heights_perm[0], educations_perm[0] ],
                            [ "2", names_perm[1], mothers_perm[1], smoothies_perm[1], heights_perm[1], educations_perm[1] ],
                            [ "3", names_perm[2], mothers_perm[2], smoothies_perm[2], heights_perm[2], educations_perm[2] ],
                            [ "4", names_perm[3], mothers_perm[3], smoothies_perm[3], heights_perm[3], educations_perm[3] ]
                        ]
                        output = {
                            "solution": {
                                "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                                "rows": solution_found
                            }
                        }
                        print(json.dumps(output, indent=2))
                        return

if __name__ == "__main__":
    main()