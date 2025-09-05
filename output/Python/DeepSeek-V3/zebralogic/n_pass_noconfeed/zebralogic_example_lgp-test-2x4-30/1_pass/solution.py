import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each attribute
    names = ["Arnold", "Eric"]
    hair_colors = ["black", "brown"]
    sports = ["basketball", "soccer"]
    smoothies = ["desert", "cherry"]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            for sport_perm in permutations(sports):
                for smoothie_perm in permutations(smoothies):
                    # Create assignment for house 1
                    house1 = {
                        "House": "1",
                        "Name": name_perm[0],
                        "HairColor": hair_perm[0],
                        "FavoriteSport": sport_perm[0],
                        "Smoothie": smoothie_perm[0]
                    }
                    
                    # Create assignment for house 2
                    house2 = {
                        "House": "2",
                        "Name": name_perm[1],
                        "HairColor": hair_perm[1],
                        "FavoriteSport": sport_perm[1],
                        "Smoothie": smoothie_perm[1]
                    }
                    
                    # Check clue 1: The Desert smoothie lover is Arnold
                    clue1 = True
                    if house1["Smoothie"] == "desert" and house1["Name"] != "Arnold":
                        clue1 = False
                    if house2["Smoothie"] == "desert" and house2["Name"] != "Arnold":
                        clue1 = False
                    
                    # Check clue 2: The person who has brown hair is the person who loves basketball
                    clue2 = True
                    if house1["HairColor"] == "brown" and house1["FavoriteSport"] != "basketball":
                        clue2 = False
                    if house2["HairColor"] == "brown" and house2["FavoriteSport"] != "basketball":
                        clue2 = False
                    
                    # Check clue 3: Arnold is somewhere to the left of the person who has black hair
                    clue3 = True
                    arnold_house = None
                    black_hair_house = None
                    
                    if house1["Name"] == "Arnold":
                        arnold_house = 1
                    if house2["Name"] == "Arnold":
                        arnold_house = 2
                    
                    if house1["HairColor"] == "black":
                        black_hair_house = 1
                    if house2["HairColor"] == "black":
                        black_hair_house = 2
                    
                    if arnold_house is None or black_hair_house is None or arnold_house >= black_hair_house:
                        clue3 = False
                    
                    # If all clues are satisfied, return the solution
                    if clue1 and clue2 and clue3:
                        return [house1, house2]
    
    return None

def main():
    solution = solve_puzzle()
    
    if solution:
        # Format the solution as required
        header = ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"]
        rows = []
        
        for house in solution:
            rows.append([
                house["House"],
                house["Name"],
                house["HairColor"],
                house["FavoriteSport"],
                house["Smoothie"]
            ])
        
        # Sort by house number to ensure correct order
        rows.sort(key=lambda x: int(x[0]))
        
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()