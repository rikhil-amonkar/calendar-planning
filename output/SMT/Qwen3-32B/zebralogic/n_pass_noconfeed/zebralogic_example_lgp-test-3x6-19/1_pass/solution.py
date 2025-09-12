from z3 import *

# Define EnumSorts
Names, (Arnold, Eric, Peter) = EnumSort('Names', ['Arnold', 'Eric', 'Peter'])
Cigars, (pall_mall, blue_master, prince) = EnumSort('Cigars', ['pall_mall', 'blue_master', 'prince'])
Animals, (horse, cat, bird) = EnumSort('Animals', ['horse', 'cat', 'bird'])
Children, (Bella, Fred, Meredith) = EnumSort('Children', ['Bella', 'Fred', 'Meredith'])
BookGenres, (science_fiction, romance, mystery) = EnumSort('BookGenres', ['science_fiction', 'romance', 'mystery'])
PhoneModels, (google_pixel_6, iphone_13, samsung_galaxy_s21) = EnumSort('PhoneModels', ['google_pixel_6', 'iphone_13', 'samsung_galaxy_s21'])

# Create variables for each house (0: house 1, 1: house 2, 2: house 3)
names = [Const(f'name_{i}', Names) for i in range(1,4)]
cigars = [Const(f'cigar_{i}', Cigars) for i in range(1,4)]
animals = [Const(f'animal_{i}', Animals) for i in range(1,4)]
children = [Const(f'children_{i}', Children) for i in range(1,4)]
bookgenres = [Const(f'bookgenre_{i}', BookGenres) for i in range(1,4)]
phonemodels = [Const(f'phonemodel_{i}', PhoneModels) for i in range(1,4)]

s = Solver()

# Add distinct constraints for each attribute
s.add(Distinct(names))
s.add(Distinct(cigars))
s.add(Distinct(animals))
s.add(Distinct(children))
s.add(Distinct(bookgenres))
s.add(Distinct(phonemodels))

# Add clues as constraints

# Clue 3: Pall Mall in second house
s.add(cigars[1] == pall_mall)

# Clue 10: science fiction in third house
s.add(bookgenres[2] == science_fiction)

# Clue 11: mystery not in second house
s.add(bookgenres[1] != mystery)

# Clue 1: mystery book lover's child is Fred
for i in range(3):
    s.add(If(bookgenres[i] == mystery, children[i] == Fred, True))

# Clue 2: cat lover is Eric
for i in range(3):
    s.add(If(animals[i] == cat, names[i] == Eric, True))

# Clue 4: horse keeper's child is Meredith
for i in range(3):
    s.add(If(animals[i] == horse, children[i] == Meredith, True))

# Clue 5: Bella's parent smokes Prince
for i in range(3):
    s.add(If(children[i] == Bella, cigars[i] == prince, True))

# Clue 6: iPhone 13 directly left of Samsung Galaxy S21
s.add(Or(
    And(phonemodels[0] == iphone_13, phonemodels[1] == samsung_galaxy_s21),
    And(phonemodels[1] == iphone_13, phonemodels[2] == samsung_galaxy_s21)
))

# Clue 7: Fred's parent is directly left of Arnold
s.add(Or(
    And(children[0] == Fred, names[1] == Arnold),
    And(children[1] == Fred, names[2] == Arnold)
))

# Clue 8: Peter is left of Eric
s.add(Or(
    And(names[0] == Peter, names[1] == Eric),
    And(names[0] == Peter, names[2] == Eric),
    And(names[1] == Peter, names[2] == Eric)
))

# Clue 9: science fiction lover uses Samsung Galaxy S21
for i in range(3):
    s.add(If(bookgenres[i] == science_fiction, phonemodels[i] == samsung_galaxy_s21, True))

# Now check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    # Mappings to convert enum strings to problem strings
    cigar_map = {
        'pall_mall': 'pall mall',
        'blue_master': 'blue master',
        'prince': 'prince'
    }
    phone_map = {
        'google_pixel_6': 'google pixel 6',
        'iphone_13': 'iphone 13',
        'samsung_galaxy_s21': 'samsung galaxy s21'
    }
    bookgenre_map = {
        'science_fiction': 'science fiction',
        'romance': 'romance',
        'mystery': 'mystery'
    }
    animal_map = {
        'horse': 'horse',
        'cat': 'cat',
        'bird': 'bird'
    }
    children_map = {
        'Bella': 'Bella',
        'Fred': 'Fred',
        'Meredith': 'Meredith'
    }
    names_map = {
        'Arnold': 'Arnold',
        'Eric': 'Eric',
        'Peter': 'Peter'
    }

    # Now extract the solution for each house
    solution = []
    for i in range(3):
        house_num = i + 1
        name_val = names_map[str(m.evaluate(names[i]))]
        cigar_val = cigar_map[str(m.evaluate(cigars[i]))]
        animal_val = animal_map[str(m.evaluate(animals[i]))]
        child_val = children_map[str(m.evaluate(children[i]))]
        book_val = bookgenre_map[str(m.evaluate(bookgenres[i]))]
        phone_val = phone_map[str(m.evaluate(phonemodels[i]))]
        solution.append([
            str(house_num),
            name_val,
            cigar_val,
            animal_val,
            child_val,
            book_val,
            phone_val
        ])
    # Output as JSON
    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
            "rows": solution
        }
    }, indent=2))
else:
    print("No solution found.")