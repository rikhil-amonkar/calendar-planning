import itertools
import json

def solve():
    names = ["Peter", "Alice", "Eric", "Arnold"]
    mothers = ["Janelle", "Holly", "Aniya", "Kailyn"]
    smoothies = ["watermelon", "dragonfruit", "desert", "cherry"]
    heights = ["tall", "average", "short", "very short"]
    educations = ["high school", "associate", "master", "bachelor"]

    # We'll generate all assignments by taking permutations for each category.
    # Houses are numbered 0 to 3 corresponding to houses 1 to 4.
    for perm_names in itertools.permutations(names):
        # Enforce: The person who is tall is Alice (clue12)
        # We also know from clue12 and clue9 that the tall person (with mother Janelle) is in one fixed house.
        # We choose house 3 (index 2) for Alice.
        if perm_names[2] != "Alice":
            continue

        for perm_mothers in itertools.permutations(mothers):
            # Clue1 & Clue9: The person whose mother's name is Janelle is in the third house.
            if perm_mothers[2] != "Janelle":
                continue

            for perm_smoothies in itertools.permutations(smoothies):
                # Clue3: The Desert smoothie lover is not in the first house.
                if perm_smoothies[0] == "desert":
                    continue

                for perm_heights in itertools.permutations(heights):
                    # Clue9 & Clue12: The person who is tall has mother Janelle and that person is Alice.
                    # Thus house 3 (index 2) must be tall.
                    if perm_heights[2] != "tall":
                        continue

                    for perm_educations in itertools.permutations(educations):
                        # Clue6: The person with a high school diploma is not in the third house.
                        if perm_educations[2] == "high school":
                            continue

                        # Build the candidate assignment for each house (index 0 to 3)
                        houses = []
                        for i in range(4):
                            houses.append({
                                "name": perm_names[i],
                                "mother": perm_mothers[i],
                                "smoothie": perm_smoothies[i],
                                "height": perm_heights[i],
                                "education": perm_educations[i]
                            })

                        valid = True

                        # Clue2: The Desert smoothie lover is the person with a master's degree.
                        # That is, if smoothie=="desert" then education must be "master", and vice versa.
                        for house in houses:
                            if house["smoothie"] == "desert" and house["education"] != "master":
                                valid = False
                                break
                            if house["education"] == "master" and house["smoothie"] != "desert":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue7: The person whose mother's name is Kailyn is the person with an associate's degree.
                        # Enforce it bidirectionally.
                        for house in houses:
                            if house["mother"] == "Kailyn" and house["education"] != "associate":
                                valid = False
                                break
                            if house["education"] == "associate" and house["mother"] != "Kailyn":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue8: The person who likes Cherry smoothies is the person whose mother's name is Aniya.
                        for house in houses:
                            if house["smoothie"] == "cherry" and house["mother"] != "Aniya":
                                valid = False
                                break
                            if house["mother"] == "Aniya" and house["smoothie"] != "cherry":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue11: The Dragonfruit smoothie lover is directly left of the person who is short.
                        # There must exist an index i (0 <= i <=2) such that house[i].smoothie == "dragonfruit"
                        # and house[i+1].height == "short".
                        df_pair_found = False
                        for i in range(3):
                            if houses[i]["smoothie"] == "dragonfruit" and houses[i+1]["height"] == "short":
                                df_pair_found = True
                                break
                        if not df_pair_found:
                            continue

                        # Clue4: The person who is very short is somewhere to the left of the person with a high school diploma.
                        vs_index = None
                        hs_index = None
                        for i, house in enumerate(houses):
                            if house["height"] == "very short":
                                vs_index = i
                            if house["education"] == "high school":
                                hs_index = i
                        if vs_index is None or hs_index is None or vs_index >= hs_index:
                            continue

                        # Clue10: Arnold is somewhere to the right of the person who has an average height.
                        avg_index = None
                        arnold_index = None
                        for i, house in enumerate(houses):
                            if house["height"] == "average":
                                avg_index = i
                            if house["name"] == "Arnold":
                                arnold_index = i
                        if avg_index is None or arnold_index is None or avg_index >= arnold_index:
                            continue

                        # Clue5: Eric and the person who likes Cherry smoothies are next to each other.
                        eric_index = None
                        cherry_index = None
                        for i, house in enumerate(houses):
                            if house["name"] == "Eric":
                                eric_index = i
                            if house["smoothie"] == "cherry":
                                cherry_index = i
                        if eric_index is None or cherry_index is None or abs(eric_index - cherry_index) != 1:
                            continue

                        # Clue12: The person who is tall is Alice.
                        for house in houses:
                            if house["height"] == "tall" and house["name"] != "Alice":
                                valid = False
                                break
                            if house["name"] == "Alice" and house["height"] != "tall":
                                valid = False
                                break
                        if not valid:
                            continue

                        # Clue6 already enforced (high school not in house 3) above.
                        # Clue3 already enforced (desert not in first house) above.
                        # Clue1 is enforced by mother in house 3.
                        # Clue2,7,8 have been enforced.
                        # Clue9 is enforced by house 3 having Janelle and height "tall".

                        # If all constraints are satisfied, we output the solution.
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                                "rows": [
                                    [str(i+1), 
                                     houses[i]["name"], 
                                     houses[i]["mother"], 
                                     houses[i]["smoothie"], 
                                     houses[i]["height"], 
                                     houses[i]["education"]]
                                    for i in range(4)
                                ]
                            }
                        }
                        print(json.dumps(solution, indent=2))
                        return

if __name__ == "__main__":
    solve()