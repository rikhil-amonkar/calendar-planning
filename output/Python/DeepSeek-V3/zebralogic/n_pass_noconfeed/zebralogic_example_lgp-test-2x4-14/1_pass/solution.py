import json
from itertools import permutations

def main():
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
                    # Create assignment for house 1 and house 2
                    assignment = [
                        {
                            "House": "1",
                            "Name": name_perm[0],
                            "HouseStyle": style_perm[0],
                            "Smoothie": smoothie_perm[0],
                            "Pet": pet_perm[0]
                        },
                        {
                            "House": "2", 
                            "Name": name_perm[1],
                            "HouseStyle": style_perm[1],
                            "Smoothie": smoothie_perm[1],
                            "Pet": pet_perm[1]
                        }
                    ]
                    
                    # Check if all attributes are unique across houses
                    valid = True
                    for i in range(2):
                        for j in range(i+1, 2):
                            if (assignment[i]["Name"] == assignment[j]["Name"] or
                                assignment[i]["HouseStyle"] == assignment[j]["HouseStyle"] or
                                assignment[i]["Smoothie"] == assignment[j]["Smoothie"] or
                                assignment[i]["Pet"] == assignment[j]["Pet"]):
                                valid = False
                                break
                        if not valid:
                            break
                    
                    if not valid:
                        continue
                    
                    # Check clue 1: Cherry smoothie owner owns a dog
                    cherry_dog = True
                    for house in assignment:
                        if house["Smoothie"] == "cherry" and house["Pet"] != "dog":
                            cherry_dog = False
                            break
                        if house["Pet"] == "dog" and house["Smoothie"] != "cherry":
                            cherry_dog = False
                            break
                    
                    if not cherry_dog:
                        continue
                    
                    # Check clue 2: Victorian house owner owns a dog
                    victorian_dog = True
                    for house in assignment:
                        if house["HouseStyle"] == "victorian" and house["Pet"] != "dog":
                            victorian_dog = False
                            break
                        if house["Pet"] == "dog" and house["HouseStyle"] != "victorian":
                            victorian_dog = False
                            break
                    
                    if not victorian_dog:
                        continue
                    
                    # Check clue 3: Victorian house is left of Eric
                    victorian_left_of_eric = False
                    victorian_house = None
                    eric_house = None
                    
                    for house in assignment:
                        if house["HouseStyle"] == "victorian":
                            victorian_house = int(house["House"])
                        if house["Name"] == "Eric":
                            eric_house = int(house["House"])
                    
                    if victorian_house is not None and eric_house is not None:
                        if victorian_house < eric_house:
                            victorian_left_of_eric = True
                    
                    if not victorian_left_of_eric:
                        continue
                    
                    # If we get here, we found a valid solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
                            "rows": [
                                [assignment[0]["House"], assignment[0]["Name"], assignment[0]["HouseStyle"], assignment[0]["Smoothie"], assignment[0]["Pet"]],
                                [assignment[1]["House"], assignment[1]["Name"], assignment[1]["HouseStyle"], assignment[1]["Smoothie"], assignment[1]["Pet"]]
                            ]
                        }
                    }
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    # If no solution found (shouldn't happen with valid puzzle)
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()