import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    
    # Define variables for each attribute
    names = ["Arnold", "Eric"]
    sports = ["basketball", "soccer"]
    hair_colors = ["brown", "black"]
    heights = ["very short", "short"]
    smoothies = ["desert", "cherry"]
    flowers = ["daffodils", "carnations"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"sport_{house}", sports)
        problem.addVariable(f"hair_{house}", hair_colors)
        problem.addVariable(f"height_{house}", heights)
        problem.addVariable(f"smoothie_{house}", smoothies)
        problem.addVariable(f"flower_{house}", flowers)
    
    # All attributes must be unique
    for attr in ["name", "sport", "hair", "height", "smoothie", "flower"]:
        problem.addConstraint(
            lambda *values: len(values) == len(set(values)),
            [f"{attr}_{house}" for house in houses]
        )
    
    # Clue 1: The person who loves soccer is not in the second house.
    problem.addConstraint(lambda sport_2: sport_2 != "soccer", ["sport_2"])
    
    # Clue 2: The Desert smoothie lover is directly left of the person who is very short.
    problem.addConstraint(
        lambda smoothie_1, smoothie_2, height_1, height_2: 
        (smoothie_1 == "desert" and height_2 == "very short") or
        (smoothie_2 == "desert" and height_1 == "very short"),
        ["smoothie_1", "smoothie_2", "height_1", "height_2"]
    )
    
    # Clue 3: The person who is very short is the person who has brown hair.
    problem.addConstraint(
        lambda height_1, height_2, hair_1, hair_2:
        (height_1 == "very short" and hair_1 == "brown") or
        (height_2 == "very short" and hair_2 == "brown"),
        ["height_1", "height_2", "hair_1", "hair_2"]
    )
    
    # Clue 4: The person who loves a carnations arrangement is the Desert smoothie lover.
    problem.addConstraint(
        lambda flower_1, flower_2, smoothie_1, smoothie_2:
        (flower_1 == "carnations" and smoothie_1 == "desert") or
        (flower_2 == "carnations" and smoothie_2 == "desert"),
        ["flower_1", "flower_2", "smoothie_1", "smoothie_2"]
    )
    
    # Clue 5: Eric and the person who has brown hair are next to each other.
    problem.addConstraint(
        lambda name_1, name_2, hair_1, hair_2:
        (name_1 == "Eric" and hair_2 == "brown") or
        (name_2 == "Eric" and hair_1 == "brown"),
        ["name_1", "name_2", "hair_1", "hair_2"]
    )
    
    # Solve the puzzle
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Format the solution
    header = ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"sport_{house}"],
            solution[f"hair_{house}"],
            solution[f"height_{house}"],
            solution[f"smoothie_{house}"],
            solution[f"flower_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))