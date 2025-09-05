#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Eric", "Alice", "Peter", "Arnold"]
    hair_colors = ["blonde", "black", "red", "brown"]
    sports = ["swimming", "soccer", "basketball", "tennis"]

    solution = None

    # Iterate over all possible assignments for names, hair colors, and sports.
    for perm_names in itertools.permutations(names):
        for perm_hairs in itertools.permutations(hair_colors):
            for perm_sports in itertools.permutations(sports):
                houses = []
                # Create houses with assigned attributes (House numbers 1 to 4)
                for i in range(4):
                    houses.append({
                        "House": str(i + 1),
                        "Name": perm_names[i],
                        "HairColor": perm_hairs[i],
                        "FavoriteSport": perm_sports[i]
                    })

                valid = True

                # Constraint 1: The person who loves soccer is not in the second house.
                if houses[1]["FavoriteSport"] == "soccer":
                    continue

                # Constraint 2: Eric is the person who has blonde hair.
                for house in houses:
                    if house["Name"] == "Eric" and house["HairColor"] != "blonde":
                        valid = False
                        break
                    if house["HairColor"] == "blonde" and house["Name"] != "Eric":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
                pos_blonde = None
                pos_basketball = None
                for i, house in enumerate(houses):
                    if house["HairColor"] == "blonde":
                        pos_blonde = i
                    if house["FavoriteSport"] == "basketball":
                        pos_basketball = i
                if pos_blonde is None or pos_basketball is None or pos_blonde <= pos_basketball:
                    continue

                # Constraint 4: The person who has black hair is the person who loves tennis.
                for house in houses:
                    if house["HairColor"] == "black" and house["FavoriteSport"] != "tennis":
                        valid = False
                        break
                    if house["FavoriteSport"] == "tennis" and house["HairColor"] != "black":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 5: Arnold is somewhere to the left of the person who has red hair.
                pos_arnold = None
                pos_red = None
                for i, house in enumerate(houses):
                    if house["Name"] == "Arnold":
                        pos_arnold = i
                    if house["HairColor"] == "red":
                        pos_red = i
                if pos_arnold is None or pos_red is None or pos_arnold >= pos_red:
                    continue

                # Constraint 6: Alice is the person who loves swimming.
                for house in houses:
                    if house["Name"] == "Alice" and house["FavoriteSport"] != "swimming":
                        valid = False
                        break
                    if house["FavoriteSport"] == "swimming" and house["Name"] != "Alice":
                        valid = False
                        break
                if not valid:
                    continue

                # Constraint 7: The person who has red hair is directly left of the person who has black hair.
                found = False
                for i in range(3):  # Check pairs of adjacent houses (1-2, 2-3, 3-4)
                    if houses[i]["HairColor"] == "red" and houses[i+1]["HairColor"] == "black":
                        found = True
                        break
                if not found:
                    continue

                # All constraints satisfied; solution found.
                solution = houses
                break
            if solution is not None:
                break
        if solution is not None:
            break

    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport"],
            "rows": []
        }
    }

    if solution is not None:
        # Ensure the houses are in order of their house number.
        for house in solution:
            output["solution"]["rows"].append([
                house["House"],
                house["Name"],
                house["HairColor"],
                house["FavoriteSport"]
            ])

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()