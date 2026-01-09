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
            lambda name, hair: not (name == "Eric" and hair != "blonde") and 
                              not (hair == "blonde" and name != "Eric"),
            [f"name_{house}", f"hair_{house}"]
        )
    
    # Clue 3: The person who has blonde hair is somewhere to the right of the person who loves basketball.
    # We need to find the house numbers for blonde hair and basketball
    def blonde_right_of_basketball(*args):
        # args will be: name1, hair1, sport1, name2, hair2, sport2, name3, hair3, sport3, name4, hair4, sport4
        blonde_pos = None
        basketball_pos = None
        for i in range(0, len(args), 3):
            house_num = (i // 3) + 1
            hair = args[i + 1]
            sport = args[i + 2]
            if hair == "blonde":
                blonde_pos = house_num
            if sport == "basketball":
                basketball_pos = house_num
        return blonde_pos is not None and basketball_pos is not None and blonde_pos > basketball_pos
    
    # Flatten the list of variables
    all_vars = []
    for house in houses:
        all_vars.extend([f"name_{house}", f"hair_{house}", f"sport_{house}"])
    problem.addConstraint(blonde_right_of_basketball, all_vars)
    
    # Clue 4: The person who has black hair is the person who loves tennis.
    for house in houses:
        problem.addConstraint(
            lambda hair, sport: not (hair == "black" and sport != "tennis") and 
                              not (sport == "tennis" and hair != "black"),
            [f"hair_{house}", f"sport_{house}"]
        )
    
    # Clue 5: Arnold is somewhere to the left of the person who has red hair.
    def arnold_left_of_red_hair(*args):
        # args will be: name1, hair1, name2, hair2, name3, hair3, name4, hair4
        arnold_pos = None
        red_hair_pos = None
        for i in range(0, len(args), 2):
            house_num = (i // 2) + 1
            name = args[i]
            hair = args[i + 1]
            if name == "Arnold":
                arnold_pos = house_num
            if hair == "red":
                red_hair_pos = house_num
        return arnold_pos is not None and red_hair_pos is not None and arnold_pos < red_hair_pos
    
    name_hair_vars = []
    for house in houses:
        name_hair_vars.extend([f"name_{house}", f"hair_{house}"])
    problem.addConstraint(arnold_left_of_red_hair, name_hair_vars)
    
    # Clue 6: Alice is the person who loves swimming.
    for house in houses:
        problem.addConstraint(
            lambda name, sport: not (name == "Alice" and sport != "swimming") and 
                              not (sport == "swimming" and name != "Alice"),
            [f"name_{house}", f"sport_{house}"]
        )
    
    # Clue 7: The person who has red hair is directly left of the person who has black hair.
    def red_left_of_black(*args):
        # args will be: hair1, hair2, hair3, hair4
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