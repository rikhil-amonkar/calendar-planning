import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    vacations = ["beach", "mountain"]
    
    problem.addVariable("Name", names)
    problem.addVariable("Vacation", vacations)
    
    # Clue 1: Arnold is somewhere to the right of the person who loves beach vacations
    def clue1(name_assignments, vacation_assignments):
        arnold_house = None
        beach_house = None
        
        for house, name in name_assignments.items():
            if name == "Arnold":
                arnold_house = house
                
        for house, vacation in vacation_assignments.items():
            if vacation == "beach":
                beach_house = house
                
        if arnold_house is not None and beach_house is not None:
            return arnold_house > beach_house
        return False
    
    problem.addConstraint(clue1, ["Name", "Vacation"])
    
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Vacation"], "rows": []}}
    
    solution = solutions[0]
    
    rows = []
    for house in sorted(houses):
        name = solution["Name"][house]
        vacation = solution["Vacation"][house]
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