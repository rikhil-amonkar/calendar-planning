import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    names = ["Peter", "Arnold", "Eric", "Alice"]
    flowers = ["daffodils", "carnations", "roses", "lilies"]
    heights = ["very short", "short", "tall", "average"]
    mothers = ["Janelle", "Kailyn", "Holly", "Aniya"]
    occupations = ["engineer", "doctor", "teacher", "artist"]
    sports = ["swimming", "basketball", "tennis", "soccer"]
    
    houses = [1, 2, 3, 4]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"flower_{house}", flowers)
        problem.addVariable(f"height_{house}", heights)
        problem.addVariable(f"mother_{house}", mothers)
        problem.addVariable(f"occupation_{house}", occupations)
        problem.addVariable(f"sport_{house}", sports)
    
    # All attributes must be different
    for attr in ["name", "flower", "height", "mother", "occupation", "sport"]:
        problem.addConstraint(AllDifferentConstraint(), [f"{attr}_{house}" for house in houses])
    
    # Clue 1: The person who loves swimming is the person who loves the rose bouquet.
    for house in houses:
        problem.addConstraint(
            lambda sport, flower, h=house: not (sport == "swimming" and flower != "roses") and not (flower == "roses" and sport != "swimming"),
            [f"sport_{house}", f"flower_{house}"]
        )
    
    # Clue 2: The person who loves the rose bouquet is Eric.
    for house in houses:
        problem.addConstraint(
            lambda flower, name, h=house: not (flower == "roses" and name != "Eric") and not (name == "Eric" and flower != "roses"),
            [f"flower_{house}", f"name_{house}"]
        )
    
    # Clue 3: Arnold is the person who is tall.
    for house in houses:
        problem.addConstraint(
            lambda name, height, h=house: not (name == "Arnold" and height != "tall") and not (height == "tall" and name != "Arnold"),
            [f"name_{house}", f"height_{house}"]
        )
    
    # Clue 4: The person who loves a bouquet of daffodils is somewhere to the right of the person who is an engineer.
    for house1 in houses:
        for house2 in houses:
            if house1 <= house2:
                problem.addConstraint(
                    lambda occ, flower, h1=house1, h2=house2: not (occ == "engineer" and flower == "daffodils" and h1 >= h2),
                    [f"occupation_{house1}", f"flower_{house2}"]
                )
    
    # Clue 5: The person who loves soccer is the person who is short.
    for house in houses:
        problem.addConstraint(
            lambda sport, height, h=house: not (sport == "soccer" and height != "short") and not (height == "short" and sport != "soccer"),
            [f"sport_{house}", f"height_{house}"]
        )
    
    # Clue 6: The person who is a teacher is in the first house.
    problem.addConstraint(lambda occ: occ == "teacher", ["occupation_1"])
    
    # Clue 7: The person whose mother's name is Janelle is the person who loves a carnations arrangement.
    for house in houses:
        problem.addConstraint(
            lambda mother, flower, h=house: not (mother == "Janelle" and flower != "carnations") and not (flower == "carnations" and mother != "Janelle"),
            [f"mother_{house}", f"flower_{house}"]
        )
    
    # Clue 8: The person who loves basketball is the person who has an average height.
    for house in houses:
        problem.addConstraint(
            lambda sport, height, h=house: not (sport == "basketball" and height != "average") and not (height == "average" and sport != "basketball"),
            [f"sport_{house}", f"height_{house}"]
        )
    
    # Clue 9: Arnold is not in the third house.
    problem.addConstraint(lambda name: name != "Arnold", ["name_3"])
    
    # Clue 10: The person whose mother's name is Holly is somewhere to the right of the person who has an average height.
    for house1 in houses:
        for house2 in houses:
            if house1 >= house2:
                problem.addConstraint(
                    lambda height, mother, h1=house1, h2=house2: not (height == "average" and mother == "Holly" and h1 <= h2),
                    [f"height_{house1}", f"mother_{house2}"]
                )
    
    # Clue 11: Peter is the person who is a doctor.
    for house in houses:
        problem.addConstraint(
            lambda name, occ, h=house: not (name == "Peter" and occ != "doctor") and not (occ == "doctor" and name != "Peter"),
            [f"name_{house}", f"occupation_{house}"]
        )
    
    # Clue 12: The person whose mother's name is Aniya is Alice.
    for house in houses:
        problem.addConstraint(
            lambda mother, name, h=house: not (mother == "Aniya" and name != "Alice") and not (name == "Alice" and mother != "Aniya"),
            [f"mother_{house}", f"name_{house}"]
        )
    
    # Clue 13: Arnold is the person who loves the bouquet of lilies.
    for house in houses:
        problem.addConstraint(
            lambda name, flower, h=house: not (name == "Arnold" and flower != "lilies") and not (flower == "lilies" and name != "Arnold"),
            [f"name_{house}", f"flower_{house}"]
        )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Format the solution
    header = ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"flower_{house}"],
            solution[f"height_{house}"],
            solution[f"mother_{house}"],
            solution[f"occupation_{house}"],
            solution[f"sport_{house}"]
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))