import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"Name_{house}", names)
        problem.addVariable(f"Vacation_{house}", vacations)
    
    # All names must be different
    problem.addConstraint(lambda *names: len(set(names)) == len(names), 
                         [f"Name_{house}" for house in houses])
    
    # All vacations must be different  
    problem.addConstraint(lambda *vacations: len(set(vacations)) == len(vacations),
                         [f"Vacation_{house}" for house in houses])
    
    # Clue 1: Arnold is somewhere to the right of the person who loves beach vacations
    def clue1(name1, name2, vacation1, vacation2):
        arnold_house = None
        beach_house = None
        
        # Find which house has Arnold
        if name1 == "Arnold":
            arnold_house = 1
        elif name2 == "Arnold":
            arnold_house = 2
            
        # Find which house has beach vacation
        if vacation1 == "beach":
            beach_house = 1
        elif vacation2 == "beach":
            beach_house = 2
            
        # Arnold must be to the right of beach person
        if arnold_house is not None and beach_house is not None:
            return arnold_house > beach_house
        return False
    
    problem.addConstraint(clue1, ["Name_1", "Name_2", "Vacation_1", "Vacation_2"])
    
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Vacation"], "rows": []}}
    
    solution = solutions[0]
    
    rows = []
    for house in houses:
        name = solution[f"Name_{house}"]
        vacation = solution[f"Vacation_{house}"]
        rows.append([str(house), name, vacation])
    
    return {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))