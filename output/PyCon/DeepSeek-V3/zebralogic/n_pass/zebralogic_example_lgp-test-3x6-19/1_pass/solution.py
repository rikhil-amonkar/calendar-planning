import constraint
import json

def solve_puzzle():
    problem = constraint.Problem()
    
    houses = [1, 2, 3]
    
    # Define variables
    names = ['Arnold', 'Eric', 'Peter']
    cigars = ['pall mall', 'blue master', 'prince']
    animals = ['horse', 'cat', 'bird']
    children = ['Bella', 'Fred', 'Meredith']
    book_genres = ['science fiction', 'romance', 'mystery']
    phone_models = ['google pixel 6', 'iphone 13', 'samsung galaxy s21']
    
    # Add variables for each attribute
    for house in houses:
        problem.addVariable(f'name_{house}', names)
        problem.addVariable(f'cigar_{house}', cigars)
        problem.addVariable(f'animal_{house}', animals)
        problem.addVariable(f'child_{house}', children)
        problem.addVariable(f'book_{house}', book_genres)
        problem.addVariable(f'phone_{house}', phone_models)
    
    # All attributes must be unique per category
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'name_{h}' for h in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'cigar_{h}' for h in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'animal_{h}' for h in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'child_{h}' for h in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'book_{h}' for h in houses])
    problem.addConstraint(constraint.AllDifferentConstraint(), [f'phone_{h}' for h in houses])
    
    # Clue 1: The person who loves mystery books is the person's child is named Fred.
    problem.addConstraint(lambda book, child: book == 'mystery' and child == 'Fred', 
                         ('book_1', 'child_1'))
    problem.addConstraint(lambda book, child: book == 'mystery' and child == 'Fred', 
                         ('book_2', 'child_2'))
    problem.addConstraint(lambda book, child: book == 'mystery' and child == 'Fred', 
                         ('book_3', 'child_3'))
    
    # Clue 2: The cat lover is Eric.
    problem.addConstraint(lambda animal, name: animal == 'cat' and name == 'Eric', 
                         ('animal_1', 'name_1'))
    problem.addConstraint(lambda animal, name: animal == 'cat' and name == 'Eric', 
                         ('animal_2', 'name_2'))
    problem.addConstraint(lambda animal, name: animal == 'cat' and name == 'Eric', 
                         ('animal_3', 'name_3'))
    
    # Clue 3: The person partial to Pall Mall is in the second house.
    problem.addConstraint(lambda cigar: cigar == 'pall mall', ('cigar_2',))
    
    # Clue 4: The person who keeps horses is the person's child is named Meredith.
    problem.addConstraint(lambda animal, child: animal == 'horse' and child == 'Meredith', 
                         ('animal_1', 'child_1'))
    problem.addConstraint(lambda animal, child: animal == 'horse' and child == 'Meredith', 
                         ('animal_2', 'child_2'))
    problem.addConstraint(lambda animal, child: animal == 'horse' and child == 'Meredith', 
                         ('animal_3', 'child_3'))
    
    # Clue 5: The person's child is named Bella is the Prince smoker.
    problem.addConstraint(lambda child, cigar: child == 'Bella' and cigar == 'prince', 
                         ('child_1', 'cigar_1'))
    problem.addConstraint(lambda child, cigar: child == 'Bella' and cigar == 'prince', 
                         ('child_2', 'cigar_2'))
    problem.addConstraint(lambda child, cigar: child == 'Bella' and cigar == 'prince', 
                         ('child_3', 'cigar_3'))
    
    # Clue 6: The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
    problem.addConstraint(lambda phone1, phone2: (phone1 == 'iphone 13' and phone2 == 'samsung galaxy s21'), 
                         ('phone_1', 'phone_2'))
    problem.addConstraint(lambda phone2, phone3: (phone2 == 'iphone 13' and phone3 == 'samsung galaxy s21'), 
                         ('phone_2', 'phone_3'))
    
    # Clue 7: The person's child is named Fred is directly left of Arnold.
    problem.addConstraint(lambda child1, name2: child1 == 'Fred' and name2 == 'Arnold', 
                         ('child_1', 'name_2'))
    problem.addConstraint(lambda child2, name3: child2 == 'Fred' and name3 == 'Arnold', 
                         ('child_2', 'name_3'))
    
    # Clue 8: Peter is somewhere to the left of Eric.
    def peter_left_of_eric(*names):
        peter_pos = None
        eric_pos = None
        for i, name in enumerate(names):
            if name == 'Peter':
                peter_pos = i + 1
            if name == 'Eric':
                eric_pos = i + 1
        return peter_pos is not None and eric_pos is not None and peter_pos < eric_pos
    
    problem.addConstraint(peter_left_of_eric, ['name_1', 'name_2', 'name_3'])
    
    # Clue 9: The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
    problem.addConstraint(lambda book, phone: book == 'science fiction' and phone == 'samsung galaxy s21', 
                         ('book_1', 'phone_1'))
    problem.addConstraint(lambda book, phone: book == 'science fiction' and phone == 'samsung galaxy s21', 
                         ('book_2', 'phone_2'))
    problem.addConstraint(lambda book, phone: book == 'science fiction' and phone == 'samsung galaxy s21', 
                         ('book_3', 'phone_3'))
    
    # Clue 10: The person who loves science fiction books is in the third house.
    problem.addConstraint(lambda book: book == 'science fiction', ('book_3',))
    
    # Clue 11: The person who loves mystery books is not in the second house.
    problem.addConstraint(lambda book: book != 'mystery', ('book_2',))
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f'name_{house}'],
            solution[f'cigar_{house}'],
            solution[f'animal_{house}'],
            solution[f'child_{house}'],
            solution[f'book_{house}'],
            solution[f'phone_{house}']
        ]
        rows.append(row)
    
    return {"solution": {"header": header, "rows": rows}}

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))