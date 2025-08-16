from z3 import *
import json

# Define the enums for Name, Smoothie, and BookGenre
Name = Datatype('Name')
Name.declare('Eric')
Name.declare('Arnold')
Name.declare('Peter')
Name = Name.create()

Smoothie = Datatype('Smoothie')
Smoothie.declare('desert')
Smoothie.declare('watermelon')
Smoothie.declare('cherry')
Smoothie = Smoothie.create()

Book = Datatype('Book')
Book.declare('science_fiction')
Book.declare('romance')
Book.declare('mystery')
Book = Book.create()

# Create variables for each house (index 0 for house1, 1 for house2, 2 for house3)
names = [Const('name_%d' % i, Name) for i in range(3)]
smoothies = [Const('smoothie_%d' % i, Smoothie) for i in range(3)]
books = [Const('book_%d' % i, Book) for i in range(3)]

solver = Solver()

# All names, smoothies, and books are distinct
solver.add(Distinct(names))
solver.add(Distinct(smoothies))
solver.add(Distinct(books))

# Clue 5: Peter is in the first house
solver.add(names[0] == Name.Peter)

# Clue 2: Arnold is the person who loves mystery books
for i in range(3):
    solver.add(If(names[i] == Name.Arnold, books[i] == Book.mystery, True))

# Clue 4: Desert smoothie lover is directly left of the mystery book lover
solver.add(Or(
    And(books[1] == Book.mystery, smoothies[0] == Smoothie.desert),
    And(books[2] == Book.mystery, smoothies[1] == Smoothie.desert)
))

# Clue 1: Cherry smoothie lover is left of the mystery book lover
solver.add(Or(
    And(smoothies[0] == Smoothie.cherry, Or(books[1] == Book.mystery, books[2] == Book.mystery)),
    And(smoothies[1] == Smoothie.cherry, books[2] == Book.mystery)
))

# Clue 3: Science fiction book lover is not in the first house
solver.add(books[0] != Book.science_fiction)

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    
    # Dictionaries to map enum values to strings
    name_dict = {
        Name.Eric: "Eric",
        Name.Arnold: "Arnold",
        Name.Peter: "Peter"
    }
    smoothie_dict = {
        Smoothie.desert: "desert",
        Smoothie.watermelon: "watermelon",
        Smoothie.cherry: "cherry"
    }
    book_dict = {
        Book.science_fiction: "science fiction",
        Book.romance: "romance",
        Book.mystery: "mystery"
    }
    
    rows = []
    for i in range(3):
        n_val = model.eval(names[i])
        s_val = model.eval(smoothies[i])
        b_val = model.eval(books[i])
        
        n_str = name_dict[n_val]
        s_str = smoothie_dict[s_val]
        b_str = book_dict[b_val]
        
        rows.append([str(i+1), n_str, s_str, b_str])
    
    solution_dict = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": rows
        }
    }
    print(json.dumps(solution_dict, indent=2))
else:
    print("No solution found")