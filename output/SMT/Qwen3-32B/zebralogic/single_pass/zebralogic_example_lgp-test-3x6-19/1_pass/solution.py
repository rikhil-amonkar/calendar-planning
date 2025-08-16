from z3 import *
import json

# Define the Z3 solver
s = Solver()

# Create variables for each house (0, 1, 2) for each attribute
names = [Int(f'name_{i}') for i in range(3)]
cigars = [Int(f'cigar_{i}') for i in range(3)]
animals = [Int(f'animal_{i}') for i in range(3)]
children = [Int(f'child_{i}') for i in range(3)]
bookgenres = [Int(f'book_{i}') for i in range(3)]
phones = [Int(f'phone_{i}') for i in range(3)]

# Add constraints for each attribute to be in 0-2 and distinct
for var_list in [names, cigars, animals, children, bookgenres, phones]:
    for var in var_list:
        s.add(And(0 <= var, var < 3))
    s.add(Distinct(var_list))

# Add specific clues
# Clue3: Pall Mall in house 2 (index 1)
s.add(cigars[1] == 0)  # Pall Mall is 0

# Clue10: science fiction in house 3 (index 2)
s.add(bookgenres[2] == 0)  # science fiction is 0

# Clue11: mystery (2) not in house 2 (index 1)
s.add(bookgenres[1] != 2)

# Clue9: science fiction (house 3) uses Samsung (2)
s.add(phones[2] == 2)  # Samsung galaxy s21 is 2

# Clue6: iPhone (1) directly left of Samsung (2). Since Samsung is in house 3 (index 2), iPhone must be in house 2 (index 1)
s.add(phones[1] == 1)  # iphone 13 is 1

# Clue5: child Bella (0) → Prince (2)
for i in range(3):
    s.add(Implies(children[i] == 0, cigars[i] == 2))

# Clue1: book mystery (2) → child Fred (1)
for i in range(3):
    s.add(Implies(bookgenres[i] == 2, children[i] == 1))

# Clue4: animal horse (0) → child Meredith (2)
for i in range(3):
    s.add(Implies(animals[i] == 0, children[i] == 2))

# Clue2: Eric (1) → cat (1)
for i in range(3):
    s.add(Implies(names[i] == 1, animals[i] == 1))

# Clue7: child Fred (1) directly left of Arnold (0)
s.add(Or(
    And(children[0] == 1, names[1] == 0),
    And(children[1] == 1, names[2] == 0)
))

# Clue8: Peter (2) is left of Eric (1)
s.add(Or(
    And(names[0] == 2, Or(names[1] == 1, names[2] == 1)),
    And(names[1] == 2, names[2] == 1)
))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    
    # Mapping from integer codes to strings
    name_map = {0: 'Arnold', 1: 'Eric', 2: 'Peter'}
    cigar_map = {0: 'pall mall', 1: 'blue master', 2: 'prince'}
    animal_map = {0: 'horse', 1: 'cat', 2: 'bird'}
    children_map = {0: 'Bella', 1: 'Fred', 2: 'Meredith'}
    bookgenre_map = {0: 'science fiction', 1: 'romance', 2: 'mystery'}
    phonemodel_map = {0: 'google pixel 6', 1: 'iphone 13', 2: 'samsung galaxy s21'}
    
    # Prepare the solution rows
    rows = []
    for i in range(3):
        house_num = i + 1
        name_val = model[names[i]].as_long()
        cigar_val = model[cigars[i]].as_long()
        animal_val = model[animals[i]].as_long()
        child_val = model[children[i]].as_long()
        book_val = model[bookgenres[i]].as_long()
        phone_val = model[phones[i]].as_long()
        row = [
            str(house_num),
            name_map[name_val],
            cigar_map[cigar_val],
            animal_map[animal_val],
            children_map[child_val],
            bookgenre_map[book_val],
            phonemodel_map[phone_val]
        ]
        rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
            "rows": rows
        }
    }
    
    # Print the solution in JSON format
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")