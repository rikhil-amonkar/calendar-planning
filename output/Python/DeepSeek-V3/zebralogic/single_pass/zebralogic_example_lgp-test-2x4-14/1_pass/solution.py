import json
from itertools import permutations

def solve_puzzle():
    # Define the attributes
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]
    smoothies = ["cherry", "desert"]
    pets = ["dog", "cat"]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for style_perm in permutations(house_styles):
            for smoothie_perm in permutations(smoothies):
                for pet_perm in permutations(pets):
                    # Assign to houses
                    solution = {
                        1: {
                            "Name": name_perm[0],
                            "House": style_perm[0],
                            "smoothie": smoothie_perm[0],
                            "pet": pet_perm[0]
                        },
                        2: {
                            "Name": name_perm[1],
                            "House": style_perm[1],
                            "smoothie": smoothie_perm[1],
                            "pet": pet_perm[1]
                        }
                    }
                    
                    # Check constraints
                    # Clue 1: Cherry smoothie owner has a dog
                    cherry_dog = True
                    for house in [1, 2]:
                        if solution[house]["smoothie"] == "cherry" and solution[house]["pet"] != "dog":
                            cherry_dog = False
                            break
                    if not cherry_dog:
                        continue
                    
                    # Clue 2: Victorian house owner has a dog
                    victorian_dog = True
                    for house in [1, 2]:
                        if solution[house]["House"] == "victorian" and solution[house]["pet"] != "dog":
                            victorian_dog = False
                            break
                    if not victorian_dog:
                        continue
                    
                    # Clue 3: Victorian house is left of Eric
                    victorian_left_eric = False
                    if solution[1]["House"] == "victorian" and solution[2]["Name"] == "Eric":
                        victorian_left_eric = True
                    if not victorian_left_eric:
                        continue
                    
                    # If all constraints are satisfied, return the solution
                    result = {
                        "solution": {
                            "header": ["House", "Name", "House", "smoothie", "pet"],
                            "rows": [
                                ["1", solution[1]["Name"], solution[1]["House"], solution[1]["smoothie"], solution[1]["pet"]],
                                ["2", solution[2]["Name"], solution[2]["House"], solution[2]["smoothie"], solution[2]["pet"]]
                        }
                    }
                    return json.dumps(result, indent=2)
    
    return json.dumps({"solution": {}})

print(solve_puzzle())