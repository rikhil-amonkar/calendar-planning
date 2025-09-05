import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4]
    names = ["Eric", "Alice", "Peter", "Arnold"]
    hair_colors = ["blonde", "black", "red", "brown"]
    sports = ["swimming", "soccer", "basketball", "tennis"]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for hair_perm in permutations(hair_colors):
            for sport_perm in permutations(sports):
                assignment = list(zip(houses, name_perm, hair_perm, sport_perm))
                
                # Check all constraints
                valid = True
                
                # Clue 1: The person who loves soccer is not in the second house.
                soccer_house = next(house for house, name, hair, sport in assignment if sport == "soccer")
                if soccer_house == 2:
                    valid = False
                
                # Clue 2: Eric is the person who has blonde hair.
                if valid:
                    eric_entry = next((name, hair) for house, name, hair, sport in assignment if name == "Eric")
                    if eric_entry[1] != "blonde":
                        valid = False
                
                # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
                if valid:
                    blonde_house = next(house for house, name, hair, sport in assignment if hair == "blonde")
                    basketball_house = next(house for house, name, hair, sport in assignment if sport == "basketball")
                    if blonde_house <= basketball_house:
                        valid = False
                
                # Clue 4: The person who has black hair is the person who loves tennis.
                if valid:
                    black_hair_entry = next((name, sport) for house, name, hair, sport in assignment if hair == "black")
                    if black_hair_entry[1] != "tennis":
                        valid = False
                
                # Clue 5: Arnold is somewhere to the left of the person who has red hair.
                if valid:
                    arnold_house = next(house for house, name, hair, sport in assignment if name == "Arnold")
                    red_hair_house = next(house for house, name, hair, sport in assignment if hair == "red")
                    if arnold_house >= red_hair_house:
                        valid = False
                
                # Clue 6: Alice is the person who loves swimming.
                if valid:
                    alice_entry = next((name, sport) for house, name, hair, sport in assignment if name == "Alice")
                    if alice_entry[1] != "swimming":
                        valid = False
                
                # Clue 7: The person who has red hair is directly left of the person who has black hair.
                if valid:
                    red_hair_house = next(house for house, name, hair, sport in assignment if hair == "red")
                    black_hair_house = next(house for house, name, hair, sport in assignment if hair == "black")
                    if black_hair_house - red_hair_house != 1:
                        valid = False
                
                if valid:
                    # Format the solution
                    rows = []
                    for house, name, hair, sport in assignment:
                        rows.append([str(house), name, hair, sport])
                    
                    result = {
                        "solution": {
                            "header": ["House", "Name", "HairColor", "FavoriteSport"],
                            "rows": rows
                        }
                    }
                    
                    print(json.dumps(result, indent=2))
                    return
    
    print('{"solution": {"header": ["House", "Name", "HairColor", "FavoriteSport"], "rows": []}}')

if __name__ == "__main__":
    main()