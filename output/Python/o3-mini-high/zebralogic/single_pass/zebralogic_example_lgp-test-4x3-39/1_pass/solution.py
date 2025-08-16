#!/usr/bin/env python3
import itertools
import json

def solve():
    names = ["Eric", "Alice", "Peter", "Arnold"]
    hair_colors = ["blonde", "black", "red", "brown"]
    sports = ["swimming", "soccer", "basketball", "tennis"]
    
    # There are 4 houses. We'll label them with indices 0,1,2,3 (house 1 = index 0, etc.)
    for perm_names in itertools.permutations(names):
        for perm_hair in itertools.permutations(hair_colors):
            for perm_sport in itertools.permutations(sports):
                houses = []
                for i in range(4):
                    houses.append({
                        "Name": perm_names[i],
                        "HairColor": perm_hair[i],
                        "FavoriteSport": perm_sport[i]
                    })
                    
                # Clue 1: The person who loves soccer is not in the second house.
                if houses[1]["FavoriteSport"] == "soccer":
                    continue
                
                # Clue 2: Eric is the person who has blonde hair.
                idx_eric = next(i for i, house in enumerate(houses) if house["Name"] == "Eric")
                if houses[idx_eric]["HairColor"] != "blonde":
                    continue
                
                # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
                idx_blonde = next(i for i, house in enumerate(houses) if house["HairColor"] == "blonde")
                idx_basketball = next(i for i, house in enumerate(houses) if house["FavoriteSport"] == "basketball")
                if idx_blonde <= idx_basketball:
                    continue
                
                # Clue 4: The person who has black hair is the person who loves tennis.
                idx_black = next(i for i, house in enumerate(houses) if house["HairColor"] == "black")
                if houses[idx_black]["FavoriteSport"] != "tennis":
                    continue
                
                # Clue 5: Arnold is somewhere to the left of the person who has red hair.
                idx_arnold = next(i for i, house in enumerate(houses) if house["Name"] == "Arnold")
                idx_red = next(i for i, house in enumerate(houses) if house["HairColor"] == "red")
                if idx_arnold >= idx_red:
                    continue
                
                # Clue 6: Alice is the person who loves swimming.
                idx_alice = next(i for i, house in enumerate(houses) if house["Name"] == "Alice")
                if houses[idx_alice]["FavoriteSport"] != "swimming":
                    continue
                
                # Clue 7: The person who has red hair is directly left of the person who has black hair.
                # Find the house with red hair and ensure the next house has black hair.
                if idx_red == 3:  # red cannot be in the last house because black must be immediately to its right
                    continue
                if houses[idx_red + 1]["HairColor"] != "black":
                    continue
                
                # If all constraints are satisfied, output the solution in the required JSON format.
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HairColor", "FavoriteSport"],
                        "rows": []
                    }
                }
                for i, house in enumerate(houses):
                    solution["solution"]["rows"].append([
                        str(i+1),
                        house["Name"],
                        house["HairColor"],
                        house["FavoriteSport"]
                    ])
                
                print(json.dumps(solution))
                return

if __name__ == "__main__":
    solve()