import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    sports = ["basketball", "soccer"]
    hobbies = ["photography", "gardening"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"sport_{house}", sports)
        problem.addVariable(f"hobby_{house}", hobbies)
    
    # All attributes must be unique across houses
    problem.addConstraint(lambda n1, n2: n1 != n2, ["name_1", "name_2"])
    problem.addConstraint(lambda s1, s2: s1 != s2, ["sport_1", "sport_2"])
    problem.addConstraint(lambda h1, h2: h1 != h2, ["hobby_1", "hobby_2"])
    
    # Clue 1: The person who enjoys gardening is Arnold.
    for house in houses:
        problem.addConstraint(
            lambda hobby, name, h=house: not (hobby == "gardening" and name != "Arnold"),
            [f"hobby_{house}", f"name_{house}"]
        )
    
    # Clue 2: The photography enthusiast is not in the first house.
    problem.addConstraint(lambda hobby: hobby != "photography", ["hobby_1"])
    
    # Clue 3: The person who loves soccer is not in the first house.
    problem.addConstraint(lambda sport: sport != "soccer", ["sport_1"])
    
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result structure
    header = ["House", "Name", "FavoriteSport", "Hobby"]
    rows = []
    
    for house in sorted(houses):
        name = solution[f"name_{house}"]
        sport = solution[f"sport_{house}"]
        hobby = solution[f"hobby_{house}"]
        rows.append([str(house), name, sport, hobby])
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))