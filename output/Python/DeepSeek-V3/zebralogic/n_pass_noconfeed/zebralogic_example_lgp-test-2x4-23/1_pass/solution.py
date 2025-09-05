import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ["Eric", "Arnold"]
    mothers = ["Aniya", "Holly"]
    cars = ["ford f150", "tesla model 3"]
    heights = ["short", "very short"]
    
    # Generate all possible permutations for each category
    name_perms = list(permutations(names))
    mother_perms = list(permutations(mothers))
    car_perms = list(permutations(cars))
    height_perms = list(permutations(heights))
    
    # Try all possible combinations
    for name_assignment in name_perms:
        for mother_assignment in mother_perms:
            for car_assignment in car_perms:
                for height_assignment in height_perms:
                    # Create house assignments
                    houses = [
                        {
                            "House": "1",
                            "Name": name_assignment[0],
                            "Mother": mother_assignment[0],
                            "CarModel": car_assignment[0],
                            "Height": height_assignment[0]
                        },
                        {
                            "House": "2", 
                            "Name": name_assignment[1],
                            "Mother": mother_assignment[1],
                            "CarModel": car_assignment[1],
                            "Height": height_assignment[1]
                        }
                    ]
                    
                    # Check clue 1: Tesla Model 3 owner is right of Arnold
                    arnold_house = None
                    tesla_house = None
                    for i, house in enumerate(houses):
                        if house["Name"] == "Arnold":
                            arnold_house = i
                        if house["CarModel"] == "tesla model 3":
                            tesla_house = i
                    
                    if arnold_house is not None and tesla_house is not None:
                        if not (tesla_house > arnold_house):
                            continue
                    
                    # Check clue 2: Arnold is short
                    for house in houses:
                        if house["Name"] == "Arnold" and house["Height"] != "short":
                            continue
                    
                    # Check clue 3: Mother Holly is in second house
                    if houses[1]["Mother"] != "Holly":
                        continue
                    
                    # If all clues are satisfied, we found the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "CarModel", "Height"],
                            "rows": [
                                [house["House"], house["Name"], house["Mother"], house["CarModel"], house["Height"]]
                                for house in houses
                            ]
                        }
                    }
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    # If no solution found (shouldn't happen with valid puzzle)
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()