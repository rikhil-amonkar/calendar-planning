import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    foods = ["pizza", "grilled cheese"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"food_{house}", foods)
    
    # All names and foods must be different
    problem.addConstraint(lambda n1, n2: n1 != n2, 
                         [f"name_{house}" for house in houses])
    problem.addConstraint(lambda f1, f2: f1 != f2, 
                         [f"food_{house}" for house in houses])
    
    # Clue 1: The person who is a pizza lover is in the second house
    problem.addConstraint(lambda food: food == "pizza", ["food_2"])
    
    # Clue 2: Arnold is not in the first house
    problem.addConstraint(lambda name: name != "Arnold", ["name_1"])
    
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Food"], "rows": []}}
    
    # Convert solution to the required format
    solution = solutions[0]
    rows = []
    
    for house in sorted(houses):
        name = solution[f"name_{house}"]
        food = solution[f"food_{house}"]
        rows.append([str(house), name, food])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Food"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))