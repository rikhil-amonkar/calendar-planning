import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house
    houses = [1, 2]
    
    # Define domains for each attribute
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    heights = ['very short', 'short']
    educations = ['associate', 'high school']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'house_style_{house}', house_styles)
        problem.addVariable(f'height_{house}', heights)
        problem.addVariable(f'education_{house}', educations)
    
    # Constraint: All attributes must be unique within their category
    problem.addConstraint(lambda n1, n2: n1 != n2, ['name_1', 'name_2'])
    problem.addConstraint(lambda s1, s2: s1 != s2, ['house_style_1', 'house_style_2'])
    problem.addConstraint(lambda h1, h2: h1 != h2, ['height_1', 'height_2'])
    problem.addConstraint(lambda e1, e2: e1 != e2, ['education_1', 'education_2'])
    
    # Clue 1: The person who is short is directly left of Eric
    problem.addConstraint(
        lambda height_1, height_2, name_1, name_2: 
        (height_1 == 'short' and name_2 == 'Eric') or 
        (height_2 == 'short' and name_1 == 'Eric'),
        ['height_1', 'height_2', 'name_1', 'name_2']
    )
    
    # Clue 2: The person residing in a Victorian house is in the first house
    problem.addConstraint(lambda style: style == 'victorian', ['house_style_1'])
    
    # Clue 3: The person who is short is the person with an associate's degree
    problem.addConstraint(
        lambda height_1, height_2, education_1, education_2:
        (height_1 == 'short' and education_1 == 'associate') or
        (height_2 == 'short' and education_2 == 'associate'),
        ['height_1', 'height_2', 'education_1', 'education_2']
    )
    
    # Get the solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result in the required format
    header = ["House", "Name", "HouseStyle", "Height", "Education"]
    rows = []
    
    for house in sorted(houses):
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'house_style_{house}'],
            solution[f'height_{house}'],
            solution[f'education_{house}']
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))