import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    heights = ["short", "very short", "average"]
    
    # Add variables for each house
    problem.addVariable("name", names)
    problem.addVariable("height", heights)
    
    # All variables must have different values
    problem.addConstraint(lambda n1, n2, n3: len(set([n1, n2, n3])) == 3, 
                         ["name_1", "name_2", "name_3"])
    problem.addConstraint(lambda h1, h2, h3: len(set([h1, h2, h3])) == 3, 
                         ["height_1", "height_2", "height_3"])
    
    # Clue 1: Eric is not in the first house
    problem.addConstraint(lambda n1: n1 != "Eric", ["name_1"])
    
    # Clue 2: The person who is very short is somewhere to the left of the person who is short
    problem.addConstraint(
        lambda h1, h2, h3: 
            (h1 == "very short" and (h2 == "short" or h3 == "short")) or
            (h2 == "very short" and h3 == "short"),
        ["height_1", "height_2", "height_3"]
    )
    
    # Clue 3: The person who is very short is Eric
    problem.addConstraint(
        lambda n1, h1, n2, h2, n3, h3: 
            (n1 == "Eric" and h1 == "very short") or
            (n2 == "Eric" and h2 == "very short") or
            (n3 == "Eric" and h3 == "very short"),
        ["name_1", "height_1", "name_2", "height_2", "name_3", "height_3"]
    )
    
    # Clue 4: Arnold is not in the first house
    problem.addConstraint(lambda n1: n1 != "Arnold", ["name_1"])
    
    # Get all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Height"], "rows": []}}
    
    # Convert to the required format
    solution = solutions[0]
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        height = solution[f"height_{house}"]
        rows.append([str(house), name, height])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))