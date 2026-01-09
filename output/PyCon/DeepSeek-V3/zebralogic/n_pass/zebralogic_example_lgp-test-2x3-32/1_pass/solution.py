import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables: house numbers and attributes
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"birthday_{house}", birthdays)
        problem.addVariable(f"color_{house}", colors)
    
    # All attributes must be different across houses
    problem.addConstraint(lambda n1, n2: n1 != n2, ["name_1", "name_2"])
    problem.addConstraint(lambda b1, b2: b1 != b2, ["birthday_1", "birthday_2"])
    problem.addConstraint(lambda c1, c2: c1 != c2, ["color_1", "color_2"])
    
    # Clue 1: Eric is the person who loves yellow
    problem.addConstraint(lambda name, color: name == "Eric" if color == "yellow" else True, 
                         ["name_1", "color_1"])
    problem.addConstraint(lambda name, color: name == "Eric" if color == "yellow" else True, 
                         ["name_2", "color_2"])
    
    # Clue 2: The person whose birthday is in April is in the first house
    problem.addConstraint(lambda birthday: birthday == "april", ["birthday_1"])
    
    # Clue 3: The person who loves yellow is not in the first house
    problem.addConstraint(lambda color: color != "yellow", ["color_1"])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Birthday", "Color"], "rows": []}}
    
    # Convert solution to required format
    solution = solutions[0]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"birthday_{house}"],
            solution[f"color_{house}"]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))