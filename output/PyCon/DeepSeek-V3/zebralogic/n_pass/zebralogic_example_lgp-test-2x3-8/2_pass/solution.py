import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house
    houses = [1, 2]
    
    # Add variables for each attribute per house
    problem.addVariables(["Name_1", "Name_2"], ["Arnold", "Eric"])
    problem.addVariables(["Birthday_1", "Birthday_2"], ["april", "sept"])
    problem.addVariables(["Mother_1", "Mother_2"], ["Aniya", "Holly"])
    
    # All attributes must be different
    problem.addConstraint(lambda name1, name2: name1 != name2, ["Name_1", "Name_2"])
    problem.addConstraint(lambda b1, b2: b1 != b2, ["Birthday_1", "Birthday_2"])
    problem.addConstraint(lambda m1, m2: m1 != m2, ["Mother_1", "Mother_2"])
    
    # Clue 1: Eric is somewhere to the left of The person whose mother's name is Holly
    def clue1(name1, name2, mother1, mother2):
        eric_house = None
        holly_mother_house = None
        
        if name1 == "Eric":
            eric_house = 1
        if name2 == "Eric":
            eric_house = 2
            
        if mother1 == "Holly":
            holly_mother_house = 1
        if mother2 == "Holly":
            holly_mother_house = 2
            
        return eric_house is not None and holly_mother_house is not None and eric_house < holly_mother_house
    
    problem.addConstraint(clue1, ["Name_1", "Name_2", "Mother_1", "Mother_2"])
    
    # Clue 2: The person whose birthday is in April is in the first house
    problem.addConstraint(lambda b1: b1 == "april", ["Birthday_1"])
    
    # Get the solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Birthday", "Mother"], "rows": []}}
    
    # Convert to the required format
    solution = solutions[0]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f"Name_{house}"],
            solution[f"Birthday_{house}"],
            solution[f"Mother_{house}"]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))