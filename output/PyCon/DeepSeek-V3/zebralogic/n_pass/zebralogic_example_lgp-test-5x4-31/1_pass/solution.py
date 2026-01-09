import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each house position (1-5)
    houses = [1, 2, 3, 4, 5]
    
    # Define domains for each attribute
    names = ['Alice', 'Bob', 'Arnold', 'Eric', 'Peter']
    vacations = ['cruise', 'city', 'camping', 'beach', 'mountain']
    children = ['Bella', 'Samantha', 'Fred', 'Meredith', 'Timothy']
    nationalities = ['dane', 'norwegian', 'brit', 'german', 'swede']
    
    # Add variables for each attribute
    problem.addVariables(['name1', 'name2', 'name3', 'name4', 'name5'], names)
    problem.addVariables(['vacation1', 'vacation2', 'vacation3', 'vacation4', 'vacation5'], vacations)
    problem.addVariables(['child1', 'child2', 'child3', 'child4', 'child5'], children)
    problem.addVariables(['nationality1', 'nationality2', 'nationality3', 'nationality4', 'nationality5'], nationalities)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), ['name1', 'name2', 'name3', 'name4', 'name5'])
    problem.addConstraint(AllDifferentConstraint(), ['vacation1', 'vacation2', 'vacation3', 'vacation4', 'vacation5'])
    problem.addConstraint(AllDifferentConstraint(), ['child1', 'child2', 'child3', 'child4', 'child5'])
    problem.addConstraint(AllDifferentConstraint(), ['nationality1', 'nationality2', 'nationality3', 'nationality4', 'nationality5'])
    
    # Clue 1: The Norwegian is Peter.
    problem.addConstraint(lambda nationality, name: nationality == 'norwegian' and name == 'Peter',
                         ['nationality1', 'name1'])
    problem.addConstraint(lambda nationality, name: nationality == 'norwegian' and name == 'Peter',
                         ['nationality2', 'name2'])
    problem.addConstraint(lambda nationality, name: nationality == 'norwegian' and name == 'Peter',
                         ['nationality3', 'name3'])
    problem.addConstraint(lambda nationality, name: nationality == 'norwegian' and name == 'Peter',
                         ['nationality4', 'name4'])
    problem.addConstraint(lambda nationality, name: nationality == 'norwegian' and name == 'Peter',
                         ['nationality5', 'name5'])
    
    # Clue 2: The Swedish person is the person's child is named Bella.
    problem.addConstraint(lambda nationality, child: nationality == 'swede' and child == 'Bella',
                         ['nationality1', 'child1'])
    problem.addConstraint(lambda nationality, child: nationality == 'swede' and child == 'Bella',
                         ['nationality2', 'child2'])
    problem.addConstraint(lambda nationality, child: nationality == 'swede' and child == 'Bella',
                         ['nationality3', 'child3'])
    problem.addConstraint(lambda nationality, child: nationality == 'swede' and child == 'Bella',
                         ['nationality4', 'child4'])
    problem.addConstraint(lambda nationality, child: nationality == 'swede' and child == 'Bella',
                         ['nationality5', 'child5'])
    
    # Clue 3: The person who loves beach vacations is directly left of the person's child is named Samantha.
    problem.addConstraint(lambda vac1, vac2, vac3, vac4, vac5, child1, child2, child3, child4, child5:
                         (vac1 == 'beach' and child2 == 'Samantha') or
                         (vac2 == 'beach' and child3 == 'Samantha') or
                         (vac3 == 'beach' and child4 == 'Samantha') or
                         (vac4 == 'beach' and child5 == 'Samantha'),
                         ['vacation1', 'vacation2', 'vacation3', 'vacation4', 'vacation5',
                          'child1', 'child2', 'child3', 'child4', 'child5'])
    
    # Clue 4: The person's child is named Bella is not in the second house.
    problem.addConstraint(lambda child: child != 'Bella', ['child2'])
    
    # Clue 5: Alice is the British person.
    problem.addConstraint(lambda name, nationality: name == 'Alice' and nationality == 'brit',
                         ['name1', 'nationality1'])
    problem.addConstraint(lambda name, nationality: name == 'Alice' and nationality == 'brit',
                         ['name2', 'nationality2'])
    problem.addConstraint(lambda name, nationality: name == 'Alice' and nationality == 'brit',
                         ['name3', 'nationality3'])
    problem.addConstraint(lambda name, nationality: name == 'Alice' and nationality == 'brit',
                         ['name4', 'nationality4'])
    problem.addConstraint(lambda name, nationality: name == 'Alice' and nationality == 'brit',
                         ['name5', 'nationality5'])
    
    # Clue 6: The person who likes going on cruises is in the first house.
    problem.addConstraint(lambda vacation: vacation == 'cruise', ['vacation1'])
    
    # Clue 7: The person's child is named Meredith is in the fourth house.
    problem.addConstraint(lambda child: child == 'Meredith', ['child4'])
    
    # Clue 8: Eric is not in the fifth house.
    problem.addConstraint(lambda name: name != 'Eric', ['name5'])
    
    # Clue 9: The Swedish person is somewhere to the right of the Norwegian.
    def swede_right_of_norwegian(n1, n2, n3, n4, n5):
        norwegian_pos = None
        swede_pos = None
        for i, nat in enumerate([n1, n2, n3, n4, n5], 1):
            if nat == 'norwegian':
                norwegian_pos = i
            if nat == 'swede':
                swede_pos = i
        return swede_pos > norwegian_pos
    
    problem.addConstraint(swede_right_of_norwegian, 
                         ['nationality1', 'nationality2', 'nationality3', 'nationality4', 'nationality5'])
    
    # Clue 10: There is one house between the person's child is named Fred and the person who prefers city breaks.
    def one_house_between(child1, child2, child3, child4, child5, vac1, vac2, vac3, vac4, vac5):
        fred_positions = []
        city_positions = []
        
        for i, (child, vac) in enumerate([(child1, vac1), (child2, vac2), (child3, vac3), (child4, vac4), (child5, vac5)], 1):
            if child == 'Fred':
                fred_positions.append(i)
            if vac == 'city':
                city_positions.append(i)
                
        for fred_pos in fred_positions:
            for city_pos in city_positions:
                if abs(fred_pos - city_pos) == 2:
                    return True
        return False
    
    problem.addConstraint(one_house_between,
                         ['child1', 'child2', 'child3', 'child4', 'child5',
                          'vacation1', 'vacation2', 'vacation3', 'vacation4', 'vacation5'])
    
    # Clue 11: Bob is the person who enjoys camping trips.
    problem.addConstraint(lambda name, vacation: name == 'Bob' and vacation == 'camping',
                         ['name1', 'vacation1'])
    problem.addConstraint(lambda name, vacation: name == 'Bob' and vacation == 'camping',
                         ['name2', 'vacation2'])
    problem.addConstraint(lambda name, vacation: name == 'Bob' and vacation == 'camping',
                         ['name3', 'vacation3'])
    problem.addConstraint(lambda name, vacation: name == 'Bob' and vacation == 'camping',
                         ['name4', 'vacation4'])
    problem.addConstraint(lambda name, vacation: name == 'Bob' and vacation == 'camping',
                         ['name5', 'vacation5'])
    
    # Clue 12: The Dane is in the fifth house.
    problem.addConstraint(lambda nationality: nationality == 'dane', ['nationality5'])
    
    # Clue 13: The person who enjoys camping trips is not in the fifth house.
    problem.addConstraint(lambda vacation: vacation != 'camping', ['vacation5'])
    
    # Solve the puzzle
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Vacation", "Children", "Nationality"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    rows = []
    for i in range(1, 6):
        house_num = str(i)
        name = solution[f'name{i}']
        vacation = solution[f'vacation{i}']
        child = solution[f'child{i}']
        nationality = solution[f'nationality{i}']
        rows.append([house_num, name, vacation, child, nationality])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Children", "Nationality"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))