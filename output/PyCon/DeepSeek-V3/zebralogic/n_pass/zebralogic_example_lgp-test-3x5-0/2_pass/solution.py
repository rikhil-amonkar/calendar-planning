import json
from constraint import Problem

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3]
    
    # Define variables
    names = ['Peter', 'Arnold', 'Eric']
    genres = ['science fiction', 'mystery', 'romance']
    smoothies = ['watermelon', 'desert', 'cherry']
    birthdays = ['april', 'jan', 'sept']
    heights = ['average', 'very short', 'short']
    
    # Add variables for each house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'genre_{house}', genres)
        problem.addVariable(f'smoothie_{house}', smoothies)
        problem.addVariable(f'birthday_{house}', birthdays)
        problem.addVariable(f'height_{house}', heights)
    
    # All attributes must be different within each category
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f'name_{h}' for h in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f'genre_{h}' for h in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f'smoothie_{h}' for h in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f'birthday_{h}' for h in houses])
    problem.addConstraint(lambda a, b, c: len(set([a, b, c])) == 3, 
                         [f'height_{h}' for h in houses])
    
    # Clue 1: The person who likes Cherry smoothies is not in the second house.
    problem.addConstraint(lambda s: s != 'cherry', ['smoothie_2'])
    
    # Clue 2: Arnold is the person who loves mystery books.
    for h in houses:
        problem.addConstraint(lambda n, g: n == 'Arnold' if g == 'mystery' else True, 
                             [f'name_{h}', f'genre_{h}'])
    
    # Clue 3: The person whose birthday is in January is not in the first house.
    problem.addConstraint(lambda b: b != 'jan', ['birthday_1'])
    
    # Clue 4: The person who is very short is the person who loves romance books.
    for h in houses:
        problem.addConstraint(lambda hgt, g: hgt == 'very short' if g == 'romance' else True, 
                             [f'height_{h}', f'genre_{h}'])
    
    # Clue 5: The person who loves mystery books is the person whose birthday is in September.
    for h in houses:
        problem.addConstraint(lambda g, b: g == 'mystery' if b == 'sept' else True, 
                             [f'genre_{h}', f'birthday_{h}'])
    
    # Clue 6: The person who has an average height is the Desert smoothie lover.
    for h in houses:
        problem.addConstraint(lambda hgt, s: hgt == 'average' if s == 'desert' else True, 
                             [f'height_{h}', f'smoothie_{h}'])
    
    # Clue 7: Eric is in the first house.
    problem.addConstraint(lambda n: n == 'Eric', ['name_1'])
    
    # Clue 8: The Watermelon smoothie lover is the person who is short.
    for h in houses:
        problem.addConstraint(lambda s, hgt: s == 'watermelon' if hgt == 'short' else True, 
                             [f'smoothie_{h}', f'height_{h}'])
    
    # Clue 9: The Watermelon smoothie lover is Eric.
    for h in houses:
        problem.addConstraint(lambda n, s: s == 'watermelon' if n == 'Eric' else True, 
                             [f'name_{h}', f'smoothie_{h}'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'genre_{house}'],
            solution[f'smoothie_{house}'],
            solution[f'birthday_{house}'],
            solution[f'height_{house}']
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))