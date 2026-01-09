import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    
    # Define variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", ["Arnold", "Eric"])
        problem.addVariable(f"hair_{house}", ["black", "brown"])
        problem.addVariable(f"sport_{house}", ["basketball", "soccer"])
        problem.addVariable(f"smoothie_{house}", ["desert", "cherry"])
    
    # All attributes must be different across houses
    for attr in ["name", "hair", "sport", "smoothie"]:
        problem.addConstraint(lambda x, y: x != y, 
                            [f"{attr}_{house}" for house in houses])
    
    # Clue 1: The Desert smoothie lover is Arnold
    for house in houses:
        problem.addConstraint(
            lambda smoothie, name: not (smoothie == "desert" and name != "Arnold"),
            [f"smoothie_{house}", f"name_{house}"]
        )
        problem.addConstraint(
            lambda smoothie, name: not (name == "Arnold" and smoothie != "desert"),
            [f"smoothie_{house}", f"name_{house}"]
        )
    
    # Clue 2: The person who has brown hair is the person who loves basketball
    for house in houses:
        problem.addConstraint(
            lambda hair, sport: not (hair == "brown" and sport != "basketball"),
            [f"hair_{house}", f"sport_{house}"]
        )
        problem.addConstraint(
            lambda hair, sport: not (sport == "basketball" and hair != "brown"),
            [f"hair_{house}", f"sport_{house}"]
        )
    
    # Clue 3: Arnold is somewhere to the left of the person who has black hair
    def arnold_left_of_black_hair(name1, hair1, name2, hair2):
        arnold_house = None
        black_hair_house = None
        
        if name1 == "Arnold":
            arnold_house = 1
        if name2 == "Arnold":
            arnold_house = 2
            
        if hair1 == "black":
            black_hair_house = 1
        if hair2 == "black":
            black_hair_house = 2
            
        return arnold_house is not None and black_hair_house is not None and arnold_house < black_hair_house
    
    problem.addConstraint(arnold_left_of_black_hair, 
                         ["name_1", "hair_1", "name_2", "hair_2"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the output structure
    header = ["House", "Name", "HairColor", "FavoriteSport", "Smoothie"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"hair_{house}"],
            solution[f"sport_{house}"],
            solution[f"smoothie_{house}"]
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))