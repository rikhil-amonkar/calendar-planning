import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3]
    
    # Define variables
    names = ["Eric", "Arnold", "Peter"]
    genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"genre_{house}", genres)
        problem.addVariable(f"vacation_{house}", vacations)
    
    # All attributes must be different
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"name_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"genre_{house}" for house in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f"vacation_{house}" for house in houses])
    
    # Clue 1: Eric is directly left of Arnold
    problem.addConstraint(lambda n1, n2, n3: 
                         (n1 == "Eric" and n2 == "Arnold") or 
                         (n2 == "Eric" and n3 == "Arnold"),
                         ["name_1", "name_2", "name_3"])
    
    # Clue 2: Peter is somewhere to the right of the person who loves beach vacations
    def peter_right_of_beach(v1, v2, v3, n1, n2, n3):
        beach_house = None
        peter_house = None
        
        if v1 == "beach": beach_house = 1
        if v2 == "beach": beach_house = 2  
        if v3 == "beach": beach_house = 3
        
        if n1 == "Peter": peter_house = 1
        if n2 == "Peter": peter_house = 2
        if n3 == "Peter": peter_house = 3
        
        return peter_house > beach_house
    
    problem.addConstraint(peter_right_of_beach, 
                         ["vacation_1", "vacation_2", "vacation_3",
                          "name_1", "name_2", "name_3"])
    
    # Clue 3: Peter is the person who prefers city breaks
    problem.addConstraint(lambda n, v: (n == "Peter") == (v == "city"),
                         ["name_1", "vacation_1"])
    problem.addConstraint(lambda n, v: (n == "Peter") == (v == "city"),
                         ["name_2", "vacation_2"])
    problem.addConstraint(lambda n, v: (n == "Peter") == (v == "city"),
                         ["name_3", "vacation_3"])
    
    # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations
    def mystery_left_of_beach(g1, g2, g3, v1, v2, v3):
        mystery_house = None
        beach_house = None
        
        if g1 == "mystery": mystery_house = 1
        if g2 == "mystery": mystery_house = 2
        if g3 == "mystery": mystery_house = 3
        
        if v1 == "beach": beach_house = 1
        if v2 == "beach": beach_house = 2  
        if v3 == "beach": beach_house = 3
        
        return mystery_house < beach_house
    
    problem.addConstraint(mystery_left_of_beach,
                         ["genre_1", "genre_2", "genre_3",
                          "vacation_1", "vacation_2", "vacation_3"])
    
    # Clue 5: The person who loves science fiction books is the person who loves beach vacations
    problem.addConstraint(lambda g, v: (g == "science fiction") == (v == "beach"),
                         ["genre_1", "vacation_1"])
    problem.addConstraint(lambda g, v: (g == "science fiction") == (v == "beach"),
                         ["genre_2", "vacation_2"])
    problem.addConstraint(lambda g, v: (g == "science fiction") == (v == "beach"),
                         ["genre_3", "vacation_3"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "BookGenre", "Vacation"]
    rows = []
    
    for house in houses:
        name = solution[f"name_{house}"]
        genre = solution[f"genre_{house}"]
        vacation = solution[f"vacation_{house}"]
        rows.append([str(house), name, genre, vacation])
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))