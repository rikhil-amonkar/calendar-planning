import json
from itertools import permutations

def main():
    # Define all possible values for each attribute
    names = ["Arnold", "Eric"]
    sports = ["basketball", "soccer"]
    hair_colors = ["brown", "black"]
    heights = ["very short", "short"]
    smoothies = ["desert", "cherry"]
    flowers = ["daffodils", "carnations"]
    
    # Generate all possible permutations for each house
    for name_perm in permutations(names):
        for sport_perm in permutations(sports):
            for hair_perm in permutations(hair_colors):
                for height_perm in permutations(heights):
                    for smoothie_perm in permutations(smoothies):
                        for flower_perm in permutations(flowers):
                            # Create assignment for house 1
                            house1 = {
                                "House": "1",
                                "Name": name_perm[0],
                                "FavoriteSport": sport_perm[0],
                                "HairColor": hair_perm[0],
                                "Height": height_perm[0],
                                "Smoothie": smoothie_perm[0],
                                "Flower": flower_perm[0]
                            }
                            
                            # Create assignment for house 2
                            house2 = {
                                "House": "2",
                                "Name": name_perm[1],
                                "FavoriteSport": sport_perm[1],
                                "HairColor": hair_perm[1],
                                "Height": height_perm[1],
                                "Smoothie": smoothie_perm[1],
                                "Flower": flower_perm[1]
                            }
                            
                            # Check clue 1: The person who loves soccer is not in the second house.
                            if house2["FavoriteSport"] == "soccer":
                                continue
                            
                            # Check clue 2: The Desert smoothie lover is directly left of the person who is very short.
                            if house1["Smoothie"] == "desert" and house2["Height"] == "very short":
                                pass  # Valid case
                            elif house2["Smoothie"] == "desert":
                                continue  # Desert smoothie in right house, can't be left of anyone
                            else:
                                continue  # Desert smoothie not in house 1
                            
                            # Check clue 3: The person who is very short is the person who has brown hair.
                            if house1["Height"] == "very short" and house1["HairColor"] != "brown":
                                continue
                            if house2["Height"] == "very short" and house2["HairColor"] != "brown":
                                continue
                            
                            # Check clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
                            if house1["Flower"] == "carnations" and house1["Smoothie"] != "desert":
                                continue
                            if house2["Flower"] == "carnations" and house2["Smoothie"] != "desert":
                                continue
                            
                            # Check clue 5: Eric and the person who has brown hair are next to each other.
                            eric_house = None
                            brown_hair_house = None
                            
                            if house1["Name"] == "Eric":
                                eric_house = 1
                            if house2["Name"] == "Eric":
                                eric_house = 2
                            
                            if house1["HairColor"] == "brown":
                                brown_hair_house = 1
                            if house2["HairColor"] == "brown":
                                brown_hair_house = 2
                            
                            if eric_house is None or brown_hair_house is None:
                                continue
                            
                            if abs(eric_house - brown_hair_house) != 1:
                                continue
                            
                            # If we reach here, all constraints are satisfied
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
                                    "rows": [
                                        [house1["House"], house1["Name"], house1["FavoriteSport"], 
                                         house1["HairColor"], house1["Height"], house1["Smoothie"], house1["Flower"]],
                                        [house2["House"], house2["Name"], house2["FavoriteSport"], 
                                         house2["HairColor"], house2["Height"], house2["Smoothie"], house2["Flower"]]
                                    ]
                                }
                            }
                            
                            print(json.dumps(solution, indent=2))
                            return
    
    # If no solution found (shouldn't happen with valid puzzle)
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()