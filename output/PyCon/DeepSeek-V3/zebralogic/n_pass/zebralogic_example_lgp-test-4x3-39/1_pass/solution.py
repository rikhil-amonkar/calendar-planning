import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    names = ["Eric", "Alice", "Peter", "Arnold"]
    hair_colors = ["blonde", "black", "red", "brown"]
    sports = ["swimming", "soccer", "basketball", "tennis"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"hair_{house}", hair_colors)
        problem.addVariable(f"sport_{house}", sports)
    
    # All attributes must be different
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         [f"name_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         [f"hair_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c, d: len(set([a, b, c, d])) == 4, 
                         [f"sport_{house}" for house in houses])
    
    # Clue 1: The person who loves soccer is not in the second house.
    problem.addConstraint(lambda sport: sport != "soccer", ["sport_2"])
    
    # Clue 2: Eric is the person who has blonde hair.
    for house in houses:
        problem.addConstraint(
            lambda name, hair, h=house: not (name == "Eric" and hair != "blonde") and 
                                      not (hair == "blonde" and name != "Eric"),
            [f"name_{house}", f"hair_{house}"]
        )
    
    # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
    def blonde_right_of_basketball(*args):
        blonde_house = None
        basketball_house = None
        for i, (name, hair, sport) in enumerate(args):
            house_num = i + 1
            if hair == "blonde":
                blonde_house = house_num
            if sport == "basketball":
                basketball_house = house_num
        return blonde_house is not None and basketball_house is not None and blonde_house > basketball_house
    
    problem.addConstraint(blonde_right_of_basketball, 
                         [(f"name_{house}", f"hair_{house}", f"sport_{house}") for house in houses])
    
    # Clue 4: The person who has black hair is the person who loves tennis.
    for house in houses:
        problem.addConstraint(
            lambda hair, sport: not (hair == "black" and sport != "tennis") and 
                              not (sport == "tennis" and hair != "black"),
            [f"hair_{house}", f"sport_{house}"]
        )
    
    # Clue 5: Arnold is somewhere to the left of the person who has red hair.
    def arnold_left_of_red_hair(*args):
        arnold_house = None
        red_hair_house = None
        for i, (name, hair) in enumerate(args):
            house_num = i + 1
            if name == "Arnold":
                arnold_house = house_num
            if hair == "red":
                red_hair_house = house_num
        return arnold_house is not None and red_hair_house is not None and arnold_house < red_hair_house
    
    problem.addConstraint(arnold_left_of_red_hair, 
                         [(f"name_{house}", f"hair_{house}") for house in houses])
    
    # Clue 6: Alice is the person who loves swimming.
    for house in houses:
        problem.addConstraint(
            lambda name, sport: not (name == "Alice" and sport != "swimming") and 
                              not (sport == "swimming" and name != "Alice"),
            [f"name_{house}", f"sport_{house}"]
        )
    
    # Clue 7: The person who has red hair is directly left of the person who has black hair.
    def red_left_of_black(*args):
        for i in range(len(args) - 1):
            if args[i] == "red" and args[i + 1] == "black":
                return True
        return False
    
    problem.addConstraint(red_left_of_black, [f"hair_{house}" for house in houses])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "HairColor", "FavoriteSport"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        hair = solution[f"hair_{house}"]
        sport = solution[f"sport_{house}"]
        rows.append([str(house), name, hair, sport])
    
    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))