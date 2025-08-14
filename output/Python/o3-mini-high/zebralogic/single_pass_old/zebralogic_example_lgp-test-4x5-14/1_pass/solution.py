#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Peter", "Alice", "Eric", "Arnold"]
    mothers = ["Janelle", "Holly", "Aniya", "Kailyn"]
    smoothies = ["watermelon", "dragonfruit", "desert", "cherry"]
    heights = ["tall", "average", "short", "very short"]
    education = ["high school", "associate", "master", "bachelor"]

    # Pre-filter permutations based on fixed clues:
    # Clue 12 & combined with 9: The person who is tall is Alice, and the person with mother's name Janelle is in house 3.
    names_perms = [perm for perm in itertools.permutations(names) if perm[2] == "Alice"]
    mothers_perms = [perm for perm in itertools.permutations(mothers) if perm[2] == "Janelle"]
    # Clue 3: Desert smoothie lover is not in the first house.
    smoothies_perms = [perm for perm in itertools.permutations(smoothies) if perm[0] != "desert"]
    heights_perms = list(itertools.permutations(heights))
    # Clue 6: The person with a high school diploma is not in the third house.
    edu_perms = [perm for perm in itertools.permutations(education) if perm[2] != "high school"]

    solution_found = None

    for names_perm in names_perms:
        for mothers_perm in mothers_perms:
            for smoothies_perm in smoothies_perms:
                for heights_perm in heights_perms:
                    # Enforce clue 9 & 12: House 3 (index 2) must be tall and no other house is tall.
                    if heights_perm[2] != "tall":
                        continue
                    if any(heights_perm[i] == "tall" for i in range(4) if i != 2):
                        continue
                    for edu_perm in edu_perms:
                        valid = True
                        # Check each house for pointwise constraints.
                        for i in range(4):
                            # Clue 2: Desert smoothie lover <-> master's degree.
                            if smoothies_perm[i] == "desert" and edu_perm[i] != "master":
                                valid = False
                                break
                            if edu_perm[i] == "master" and smoothies_perm[i] != "desert":
                                valid = False
                                break
                            # Clue 7: Mother Kailyn <-> associate degree.
                            if mothers_perm[i] == "Kailyn" and edu_perm[i] != "associate":
                                valid = False
                                break
                            if edu_perm[i] == "associate" and mothers_perm[i] != "Kailyn":
                                valid = False
                                break
                            # Clue 8: Cherry smoothie lover <-> mother Aniya.
                            if smoothies_perm[i] == "cherry" and mothers_perm[i] != "Aniya":
                                valid = False
                                break
                            if mothers_perm[i] == "Aniya" and smoothies_perm[i] != "cherry":
                                valid = False
                                break
                            # Clue 9 & 12: The person who is tall is Alice and has mother Janelle.
                            if heights_perm[i] == "tall":
                                if mothers_perm[i] != "Janelle" or names_perm[i] != "Alice":
                                    valid = False
                                    break
                            if mothers_perm[i] == "Janelle":
                                if heights_perm[i] != "tall" or names_perm[i] != "Alice":
                                    valid = False
                                    break
                        if not valid:
                            continue

                        # Global constraints:

                        # Clue 4: The very short person is somewhere to the left of the high school diploma holder.
                        try:
                            vshort_index = heights_perm.index("very short")
                            hschool_index = edu_perm.index("high school")
                        except ValueError:
                            valid = False
                        if valid and not (vshort_index < hschool_index):
                            valid = False

                        # Clue 5: Eric and the cherry smoothie lover are next to each other.
                        try:
                            eric_index = names_perm.index("Eric")
                            cherry_index = smoothies_perm.index("cherry")
                        except ValueError:
                            valid = False
                        if valid and abs(eric_index - cherry_index) != 1:
                            valid = False

                        # Clue 10: Arnold is somewhere to the right of the person with average height.
                        try:
                            arnold_index = names_perm.index("Arnold")
                            avg_index = heights_perm.index("average")
                        except ValueError:
                            valid = False
                        if valid and not (avg_index < arnold_index):
                            valid = False

                        # Clue 11: The dragonfruit smoothie lover is directly left of the person who is short.
                        try:
                            df_index = smoothies_perm.index("dragonfruit")
                        except ValueError:
                            valid = False
                        if valid:
                            if df_index == 3:
                                valid = False
                            else:
                                if heights_perm[df_index + 1] != "short":
                                    valid = False

                        if valid:
                            # Construct solution as list of house dictionaries.
                            houses = []
                            for i in range(4):
                                house = {
                                    "House": str(i + 1),
                                    "Name": names_perm[i],
                                    "Mother": mothers_perm[i],
                                    "Favorite Smoothie": smoothies_perm[i],
                                    "Height": heights_perm[i],
                                    "Education": edu_perm[i]
                                }
                                houses.append(house)
                            solution_found = houses
                            break
                    if solution_found is not None:
                        break
                if solution_found is not None:
                    break
            if solution_found is not None:
                break
        if solution_found is not None:
            break

    if solution_found is not None:
        output = {
            "solution": {
                "header": ["House", "Name", "Mother", "Favorite Smoothie", "Height", "Education"],
                "rows": [[house["House"], house["Name"], house["Mother"], house["Favorite Smoothie"], house["Height"], house["Education"]] for house in solution_found]
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()