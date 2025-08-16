import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each category
    names = ["Arnold", "Eric"]
    sports = ["basketball", "soccer"]
    hair_colors = ["brown", "black"]
    heights = ["very short", "short"]
    smoothies = ["desert", "cherry"]
    flowers = ["daffodils", "carnations"]
    
    # Generate all possible permutations for each house
    for name1, name2 in permutations(names, 2):
        for sport1, sport2 in permutations(sports, 2):
            for hair1, hair2 in permutations(hair_colors, 2):
                for height1, height2 in permutations(heights, 2):
                    for smoothie1, smoothie2 in permutations(smoothies, 2):
                        for flower1, flower2 in permutations(flowers, 2):
                            house1 = {
                                "House": "1",
                                "Name": name1,
                                "FavoriteSport": sport1,
                                "HairColor": hair1,
                                "Height": height1,
                                "Smoothie": smoothie1,
                                "Flower": flower1
                            }
                            house2 = {
                                "House": "2",
                                "Name": name2,
                                "FavoriteSport": sport2,
                                "HairColor": hair2,
                                "Height": height2,
                                "Smoothie": smoothie2,
                                "Flower": flower2
                            }
                            
                            # Check all constraints
                            # Clue 1: The person who loves soccer is not in the second house.
                            if house2["FavoriteSport"] == "soccer":
                                continue
                            
                            # Clue 2: The Desert smoothie lover is directly left of the person who is very short.
                            if not (
                                (house1["Smoothie"] == "desert" and house2["Height"] == "very short") or
                                (house2["Smoothie"] == "desert" and False)  # No house to the right of house2
                            ):
                                continue
                            
                            # Clue 3: The person who is very short is the person who has brown hair.
                            if house1["Height"] == "very short" and house1["HairColor"] != "brown":
                                continue
                            if house2["Height"] == "very short" and house2["HairColor"] != "brown":
                                continue
                            
                            # Clue 4: The person who loves carnations is the Desert smoothie lover.
                            if house1["Flower"] == "carnations" and house1["Smoothie"] != "desert":
                                continue
                            if house2["Flower"] == "carnations" and house2["Smoothie"] != "desert":
                                continue
                            
                            # Clue 5: Eric and the person who has brown hair are next to each other.
                            eric_house = house1 if house1["Name"] == "Eric" else (house2 if house2["Name"] == "Eric" else None)
                            brown_hair_house = house1 if house1["HairColor"] == "brown" else (house2 if house2["HairColor"] == "brown" else None)
                            if eric_house is None or brown_hair_house is None:
                                continue
                            if abs(int(eric_house["House"]) - int(brown_hair_house["House"])) != 1:
                                continue
                            
                            # All constraints satisfied, return the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
                                    "rows": [
                                        [house1["House"], house1["Name"], house1["FavoriteSport"], house1["HairColor"], house1["Height"], house1["Smoothie"], house1["Flower"]],
                                        [house2["House"], house2["Name"], house2["FavoriteSport"], house2["HairColor"], house2["Height"], house2["Smoothie"], house2["Flower"]]
                                    ]
                                }
                            }
                            return json.dumps(solution, indent=2)
    
    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())