import constraint
import json

def solve_puzzle():
    problem = constraint.Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Carol', 'Peter', 'Eric', 'Arnold', 'Alice', 'Bob']
    cigars = ['blends', 'yellow monster', 'pall mall', 'blue master', 'dunhill', 'prince']
    
    problem.addVariables(['name'], [names])
    problem.addVariables(['cigar'], [cigars])
    
    # Clue 2: Blue Master is in the fifth house
    problem.addConstraint(lambda cigar: cigar == 'blue master', ['cigar_5'])
    
    # Clue 5: Pall Mall is in the third house
    problem.addConstraint(lambda cigar: cigar == 'pall mall', ['cigar_3'])
    
    # Clue 6: Eric is in the sixth house
    problem.addConstraint(lambda name: name == 'Eric', ['name_6'])
    
    # Clue 8: Peter is in the first house
    problem.addConstraint(lambda name: name == 'Peter', ['name_1'])
    
    # Clue 9: Bob is in the third house
    problem.addConstraint(lambda name: name == 'Bob', ['name_3'])
    
    # Clue 7: Carol and Eric are next to each other
    def adjacent_carol_eric(*names):
        carol_pos = names.index('Carol') + 1 if 'Carol' in names else -1
        eric_pos = names.index('Eric') + 1 if 'Eric' in names else -1
        return abs(carol_pos - eric_pos) == 1
    
    problem.addConstraint(adjacent_carol_eric, ['name_1', 'name_2', 'name_3', 'name_4', 'name_5', 'name_6'])
    
    # Clue 1: Arnold is left of blends smoker
    def left_of_blends(*names_cigars):
        names = names_cigars[:6]
        cigars = names_cigars[6:]
        arnold_pos = names.index('Arnold') + 1 if 'Arnold' in names else -1
        blends_pos = cigars.index('blends') + 1 if 'blends' in cigars else -1
        return arnold_pos < blends_pos
    
    problem.addConstraint(left_of_blends, ['name_1', 'name_2', 'name_3', 'name_4', 'name_5', 'name_6',
                                         'cigar_1', 'cigar_2', 'cigar_3', 'cigar_4', 'cigar_5', 'cigar_6'])
    
    # Clue 3: Arnold is left of Prince smoker
    def left_of_prince(*names_cigars):
        names = names_cigars[:6]
        cigars = names_cigars[6:]
        arnold_pos = names.index('Arnold') + 1 if 'Arnold' in names else -1
        prince_pos = cigars.index('prince') + 1 if 'prince' in cigars else -1
        return arnold_pos < prince_pos
    
    problem.addConstraint(left_of_prince, ['name_1', 'name_2', 'name_3', 'name_4', 'name_5', 'name_6',
                                         'cigar_1', 'cigar_2', 'cigar_3', 'cigar_4', 'cigar_5', 'cigar_6'])
    
    # Clue 4: One house between Yellow Monster and blends
    def one_between_yellow_blends(*cigars):
        yellow_pos = cigars.index('yellow monster') + 1 if 'yellow monster' in cigars else -1
        blends_pos = cigars.index('blends') + 1 if 'blends' in cigars else -1
        return abs(yellow_pos - blends_pos) == 2
    
    problem.addConstraint(one_between_yellow_blends, ['cigar_1', 'cigar_2', 'cigar_3', 'cigar_4', 'cigar_5', 'cigar_6'])
    
    # All names and cigars are unique
    problem.addConstraint(constraint.AllDifferentConstraint(), ['name_1', 'name_2', 'name_3', 'name_4', 'name_5', 'name_6'])
    problem.addConstraint(constraint.AllDifferentConstraint(), ['cigar_1', 'cigar_2', 'cigar_3', 'cigar_4', 'cigar_5', 'cigar_6'])
    
    # Add variables for each house
    for house in houses:
        problem.addVariables([f'name_{house}'], names)
        problem.addVariables([f'cigar_{house}'], cigars)
    
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "Cigar"], "rows": []}}
    
    solution = solutions[0]
    
    # Build the output
    rows = []
    for house in range(1, 7):
        name = solution[f'name_{house}']
        cigar = solution[f'cigar_{house}']
        rows.append([str(house), name, cigar])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Cigar"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))