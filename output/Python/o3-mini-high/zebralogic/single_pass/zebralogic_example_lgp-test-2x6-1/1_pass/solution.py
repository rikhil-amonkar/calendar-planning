#!/usr/bin/env python3
import itertools
import json

def solve_puzzle():
    # Define the possible values for each category.
    names = ["Arnold", "Eric"]
    favorite_sports = ["basketball", "soccer"]
    hair_colors = ["brown", "black"]
    heights = ["very short", "short"]
    smoothies = ["desert", "cherry"]
    flowers = ["daffodils", "carnations"]

    # There are 2 houses: index 0 represents House "1" and index 1 represents House "2".
    for name_perm in itertools.permutations(names):
        for sport_perm in itertools.permutations(favorite_sports):
            # Constraint 1: The person who loves soccer is not in the second house.
            if sport_perm[1] == "soccer":
                continue
            for hair_perm in itertools.permutations(hair_colors):
                for height_perm in itertools.permutations(heights):
                    for smoothie_perm in itertools.permutations(smoothies):
                        # Constraint 2: The Desert smoothie lover is directly left of the person who is very short.
                        # In a 2-house puzzle, that forces the Desert smoothie lover to be in House 1 (index 0)
                        # and the house immediately to its right (House 2, index 1) must be very short.
                        if smoothie_perm[0] != "desert":
                            continue
                        if height_perm[1] != "very short":
                            continue
                        for flower_perm in itertools.permutations(flowers):
                            valid = True
                            # Constraint 4: The person who loves a carnations arrangement is the Desert smoothie lover.
                            for i in range(2):
                                if (smoothie_perm[i] == "desert" and flower_perm[i] != "carnations") or (flower_perm[i] == "carnations" and smoothie_perm[i] != "desert"):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            # Constraint 3: The person who is very short is the person who has brown hair.
                            for i in range(2):
                                if (height_perm[i] == "very short" and hair_perm[i] != "brown") or (hair_perm[i] == "brown" and height_perm[i] != "very short"):
                                    valid = False
                                    break
                            if not valid:
                                continue
                            # Constraint 5: Eric and the person who has brown hair are next to each other.
                            try:
                                index_eric = name_perm.index("Eric")
                                index_brown = hair_perm.index("brown")
                            except ValueError:
                                continue
                            if abs(index_eric - index_brown) != 1:
                                continue

                            # If all constraints are satisfied, then we have found the solution.
                            solution_rows = []
                            for i in range(2):
                                house_num = str(i + 1)
                                row = [
                                    house_num,
                                    name_perm[i],
                                    sport_perm[i],
                                    hair_perm[i],
                                    height_perm[i],
                                    smoothie_perm[i],
                                    flower_perm[i]
                                ]
                                solution_rows.append(row)
                            
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
                                    "rows": solution_rows
                                }
                            }
                            print(json.dumps(result, indent=2))
                            return

if __name__ == "__main__":
    solve_puzzle()