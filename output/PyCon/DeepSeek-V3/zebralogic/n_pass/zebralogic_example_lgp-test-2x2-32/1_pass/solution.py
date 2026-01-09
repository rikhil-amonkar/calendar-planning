import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    genres = ["science fiction", "mystery"]
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"genre_{house}", genres)
    
    # All names and genres must be different
    problem.addConstraint(lambda n1, n2: n1 != n2, 
                         [f"name_{house}" for house in houses])
    problem.addConstraint(lambda g1, g2: g1 != g2, 
                         [f"genre_{house}" for house in houses])
    
    # Clue 1: Eric is directly left of the person who loves mystery books
    problem.addConstraint(
        lambda n1, n2, g1, g2: (n1 == "Eric" and g2 == "mystery") or 
                               (n2 == "Eric" and g1 == "mystery"),
        ["name_1", "name_2", "genre_1", "genre_2"]
    )
    
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "BookGenre"], "rows": []}}
    
    # Convert solution to the required format
    solution = solutions[0]
    rows = []
    
    for house in sorted(houses):
        name = solution[f"name_{house}"]
        genre = solution[f"genre_{house}"]
        rows.append([str(house), name, genre])
    
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))