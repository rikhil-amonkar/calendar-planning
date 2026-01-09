from constraint import Problem
import json

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4]
    names = ['Alice', 'Arnold', 'Peter', 'Eric']
    hair_colors = ['black', 'blonde', 'brown', 'red']
    
    # Add variables for names and hair colors
    problem.addVariables(['name_1', 'name_2', 'name_3', 'name_4'], names)
    problem.addVariables(['hair_1', 'hair_2', 'hair_3', 'hair_4'], hair_colors)
    
    # All names and hair colors must be different
    problem.addConstraint(lambda a, b, c, d: len({a, b, c, d}) == 4, 
                         ['name_1', 'name_2', 'name_3', 'name_4'])
    problem.addConstraint(lambda a, b, c, d: len({a, b, c, d}) == 4, 
                         ['hair_1', 'hair_2', 'hair_3', 'hair_4'])
    
    # Clue 1: Eric is directly left of the person who has blonde hair
    # This means Eric must be in position 1, 2, or 3, and the person to his right has blonde hair
    def eric_left_of_blonde(n1, n2, n3, n4, h1, h2, h3, h4):
        eric_positions = []
        blonde_positions = []
        
        if n1 == 'Eric': eric_positions.append(1)
        if n2 == 'Eric': eric_positions.append(2)
        if n3 == 'Eric': eric_positions.append(3)
        if n4 == 'Eric': eric_positions.append(4)
        
        if h1 == 'blonde': blonde_positions.append(1)
        if h2 == 'blonde': blonde_positions.append(2)
        if h3 == 'blonde': blonde_positions.append(3)
        if h4 == 'blonde': blonde_positions.append(4)
        
        # Eric must be directly left of blonde (position difference of 1)
        for eric_pos in eric_positions:
            for blonde_pos in blonde_positions:
                if blonde_pos - eric_pos == 1:
                    return True
        return False
    
    problem.addConstraint(eric_left_of_blonde, 
                         ['name_1', 'name_2', 'name_3', 'name_4', 
                          'hair_1', 'hair_2', 'hair_3', 'hair_4'])
    
    # Clue 2: Alice and Arnold are next to each other
    def alice_arnold_adjacent(n1, n2, n3, n4):
        alice_pos = None
        arnold_pos = None
        
        if n1 == 'Alice': alice_pos = 1
        elif n2 == 'Alice': alice_pos = 2
        elif n3 == 'Alice': alice_pos = 3
        elif n4 == 'Alice': alice_pos = 4
        
        if n1 == 'Arnold': arnold_pos = 1
        elif n2 == 'Arnold': arnold_pos = 2
        elif n3 == 'Arnold': arnold_pos = 3
        elif n4 == 'Arnold': arnold_pos = 4
        
        return abs(alice_pos - arnold_pos) == 1
    
    problem.addConstraint(alice_arnold_adjacent, ['name_1', 'name_2', 'name_3', 'name_4'])
    
    # Clue 3: Eric is the person who has brown hair
    problem.addConstraint(lambda n1, h1: not (n1 == 'Eric' and h1 != 'brown'), 
                         ['name_1', 'hair_1'])
    problem.addConstraint(lambda n2, h2: not (n2 == 'Eric' and h2 != 'brown'), 
                         ['name_2', 'hair_2'])
    problem.addConstraint(lambda n3, h3: not (n3 == 'Eric' and h3 != 'brown'), 
                         ['name_3', 'hair_3'])
    problem.addConstraint(lambda n4, h4: not (n4 == 'Eric' and h4 != 'brown'), 
                         ['name_4', 'hair_4'])
    
    # Clue 4: The person who has black hair is not in the first house
    problem.addConstraint(lambda h1: h1 != 'black', ['hair_1'])
    
    # Clue 5: Alice is in the first house
    problem.addConstraint(lambda n1: n1 == 'Alice', ['name_1'])
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "HairColor"], "rows": []}}
    
    solution = solutions[0]
    
    # Build result
    rows = []
    for i in range(1, 5):
        name = solution[f'name_{i}']
        hair_color = solution[f'hair_{i}']
        rows.append([str(i), name, hair_color])
    
    result = {
        "solution": {
            "header": ["House", "Name", "HairColor"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))