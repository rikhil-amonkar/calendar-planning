import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2]
    
    # Define variables
    names = ['Eric', 'Arnold']
    children = ['Bella', 'Fred']
    foods = ['grilled cheese', 'pizza']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'child_{house}', children)
        problem.addVariable(f'food_{house}', foods)
    
    # All attributes must be different
    problem.addConstraint(lambda n1, n2: n1 != n2, 
                         [f'name_{house}' for house in houses])
    problem.addConstraint(lambda c1, c2: c1 != c2, 
                         [f'child_{house}' for house in houses])
    problem.addConstraint(lambda f1, f2: f1 != f2, 
                         [f'food_{house}' for house in houses])
    
    # Clue 1: The person who is a pizza lover is Arnold.
    for house in houses:
        problem.addConstraint(
            lambda food, name, h=house: not (food == 'pizza' and name != 'Arnold'),
            [f'food_{house}', f'name_{house}']
        )
    
    # Clue 2: The person who loves eating grilled cheese is directly left of the person's child is named Fred.
    # This means: house 1 has grilled cheese AND house 2 has child Fred
    problem.addConstraint(lambda food1: food1 == 'grilled cheese', ['food_1'])
    problem.addConstraint(lambda child2: child2 == 'Fred', ['child_2'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Children", "Food"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in sorted(houses):
        name = solution[f'name_{house}']
        child = solution[f'child_{house}']
        food = solution[f'food_{house}']
        rows.append([str(house), name, child, food])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))