#!/usr/bin/env python3
import json
import itertools

def main():
    # Define the houses and possible attributes
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    favorite_sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]

    solution = None

    # Iterate over all possible permutations assignments for each attribute type
    for names_perm, hair_perm, sports_perm, smoothies_perm in itertools.product(
        itertools.permutations(names),
        itertools.permutations(hair_colors),
        itertools.permutations(favorite_sports),
        itertools.permutations(smoothies)
    ):
        # Build assignment for each house (house number as string)
        house_assignments = []
        for i in range(len(houses)):
            house_assignments.append({
                "House": str(houses[i]),
                "Name": names_perm[i],
                "HairColor": hair_perm[i],
                "FavoriteSport": sports_perm[i],
                "Smoothie": smoothies_perm[i]
            })

        # Constraint 1: The Desert smoothie lover is Arnold.
        valid = True
        for h in house_assignments:
            if h["Name"] == "Arnold" and h["Smoothie"] != "desert":
                valid = False
                break
        if not valid:
            continue

        # Constraint 2: The person who has brown hair is the person who loves basketball.
        for h in house_assignments:
            if h["HairColor"] == "brown" and h["FavoriteSport"] != "basketball":
                valid = False
                break
        if not valid:
            continue

        # Constraint 3: Arnold is somewhere to the left of the person who has black hair.
        try:
            ar_index = next(i for i, h in enumerate(house_assignments) if h["Name"] == "Arnold")
            black_index = next(i for i, h in enumerate(house_assignments) if h["HairColor"] == "black")
        except StopIteration:
            valid = False
        if not valid or not (ar_index < black_index):
            continue

        # If all constraints are satisfied, we have found a valid solution.
        solution = house_assignments
        break

    # Build the output structure as requested
    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"],
            "rows": []
        }
    }
    if solution:
        for h in solution:
            output["solution"]["rows"].append([
                h["House"],
                h["Name"],
                h["HairColor"],
                h["FavoriteSport"],
                h["Smoothie"]
            ])

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()