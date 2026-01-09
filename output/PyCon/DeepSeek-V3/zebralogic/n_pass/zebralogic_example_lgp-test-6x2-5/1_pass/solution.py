import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold']
    vacations = ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach']
    
    # Add variables for names and vacations per house
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'vacation_{house}', vacations)
    
    # All names and vacations must be different
    problem.addConstraint(AllDifferentConstraint(), [f'name_{house}' for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f'vacation_{house}' for house in houses])
    
    # Clue 1: cultural tours is somewhere to the left of beach vacations
    def cultural_left_of_beach(*args):
        cultural_pos = None
        beach_pos = None
        for i, vacation in enumerate(args):
            if vacation == 'cultural':
                cultural_pos = i + 1
            if vacation == 'beach':
                beach_pos = i + 1
        return cultural_pos < beach_pos
    
    problem.addConstraint(cultural_left_of_beach, [f'vacation_{house}' for house in houses])
    
    # Clue 2: Eric is somewhere to the right of Alice
    def eric_right_of_alice(*args):
        alice_pos = None
        eric_pos = None
        for i, name in enumerate(args):
            if name == 'Alice':
                alice_pos = i + 1
            if name == 'Eric':
                eric_pos = i + 1
        return eric_pos > alice_pos
    
    problem.addConstraint(eric_right_of_alice, [f'name_{house}' for house in houses])
    
    # Clue 3: Eric is in the second house
    problem.addConstraint(lambda name: name == 'Eric', ['name_2'])
    
    # Clue 4: cultural tours is in the third house
    problem.addConstraint(lambda vacation: vacation == 'cultural', ['vacation_3'])
    
    # Clue 5: Bob is directly left of Arnold
    def bob_left_of_arnold(*args):
        for i in range(len(args) - 1):
            if args[i] == 'Bob' and args[i+1] == 'Arnold':
                return True
        return False
    
    problem.addConstraint(bob_left_of_arnold, [f'name_{house}' for house in houses])
    
    # Clue 6: camping is not in the first house
    problem.addConstraint(lambda vacation: vacation != 'camping', ['vacation_1'])
    
    # Clue 7: cultural tours is Peter
    problem.addConstraint(lambda name, vacation: (vacation == 'cultural') == (name == 'Peter'), 
                         ['name_3', 'vacation_3'])
    
    # Clue 8: cruises is Bob
    for house in houses:
        problem.addConstraint(lambda name, vacation: (vacation == 'cruise') == (name == 'Bob'), 
                             [f'name_{house}', f'vacation_{house}'])
    
    # Clue 9: city breaks is in the fourth house
    problem.addConstraint(lambda vacation: vacation == 'city', ['vacation_4'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Vacation"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f'name_{house}']
        vacation = solution[f'vacation_{house}']
        rows.append([str(house), name, vacation])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))