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
    problem.addConstraint(lambda n1, n2, h1, h2: not (n1 == 'Eric' and h2 == 'blonde'), 
                         ['name_1', 'name_2', 'hair_1', 'hair_2'])
    problem.addConstraint(lambda n2, n3, h2, h3: not (n2 == 'Eric' and h3 == 'blonde'), 
                         ['name_2', 'name_3', 'hair_2', 'hair_3'])
    problem.addConstraint(lambda n3, n4, h3, h4: not (n3 == 'Eric' and h4 == 'blonde'), 
                         ['name_3', 'name_4', 'hair_3', 'hair_4'])
    
    # Make sure Eric is left of blonde hair
    problem.addConstraint(lambda n1, n2, h2: not (n1 == 'Eric' and h2 != 'blonde'), 
                         ['name_1', 'name_2', 'hair_2'])
    problem.addConstraint(lambda n2, n3, h3: not (n2 == 'Eric' and h3 != 'blonde'), 
                         ['name_2', 'name_3', 'hair_3'])
    problem.addConstraint(lambda n3, n4, h4: not (n3 == 'Eric' and h4 != 'blonde'), 
                         ['name_3', 'name_4', 'hair_4'])
    
    # Clue 2: Alice and Arnold are next to each other
    def are_adjacent(alice_pos, arnold_pos):
        return abs(alice_pos - arnold_pos) == 1
    
    problem.addConstraint(are_adjacent, 
                         [lambda n1, n2, n3, n4: 
                          [i+1 for i, name in enumerate([n1, n2, n3, n4]) if name == 'Alice'][0],
                          lambda n1, n2, n3, n4: 
                          [i+1 for i, name in enumerate([n1, n2, n3, n4]) if name == 'Arnold'][0]])
    
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