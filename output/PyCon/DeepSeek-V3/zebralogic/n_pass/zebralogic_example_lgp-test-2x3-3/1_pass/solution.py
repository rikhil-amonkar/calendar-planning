import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house
    houses = [1, 2]
    
    # Add variables for each attribute
    problem.addVariables(["name_1", "name_2"], ["Arnold", "Eric"])
    problem.addVariables(["food_1", "food_2"], ["grilled cheese", "pizza"])
    problem.addVariables(["mother_1", "mother_2"], ["Holly", "Aniya"])
    
    # All attributes must be unique within their category
    problem.addConstraint(lambda a, b: a != b, ["name_1", "name_2"])
    problem.addConstraint(lambda a, b: a != b, ["food_1", "food_2"])
    problem.addConstraint(lambda a, b: a != b, ["mother_1", "mother_2"])
    
    # Clue 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover
    problem.addConstraint(lambda f1, f2: f1 == "grilled cheese" and f2 == "pizza", ["food_1", "food_2"])
    
    # Clue 2: Arnold is not in the second house
    problem.addConstraint(lambda n2: n2 != "Arnold", ["name_2"])
    
    # Clue 3: Arnold is the person whose mother's name is Holly
    problem.addConstraint(lambda n1, n2, m1, m2: 
                         (n1 == "Arnold" and m1 == "Holly") or (n2 == "Arnold" and m2 == "Holly"),
                         ["name_1", "name_2", "mother_1", "mother_2"])
    
    # Get the solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Food", "Mother"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result in the required format
    rows = []
    for house in houses:
        row = [
            str(house),
            solution[f"name_{house}"],
            solution[f"food_{house}"],
            solution[f"mother_{house}"]
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))