from z3 import *
import json

solver = Solver()

# House 1 variables
name_1 = String('name_1')
bookgenre_1 = String('bookgenre_1')
birthday_1 = String('birthday_1')
animal_1 = String('animal_1')

# House 2 variables
name_2 = String('name_2')
bookgenre_2 = String('bookgenre_2')
birthday_2 = String('birthday_2')
animal_2 = String('animal_2')

# Add constraints for possible values and uniqueness
# Names
solver.add(Or(name_1 == 'Eric', name_1 == 'Arnold'))
solver.add(Or(name_2 == 'Eric', name_2 == 'Arnold'))
solver.add(name_1 != name_2)

# Book genres
solver.add(Or(bookgenre_1 == 'science fiction', bookgenre_1 == 'mystery'))
solver.add(Or(bookgenre_2 == 'science fiction', bookgenre_2 == 'mystery'))
solver.add(bookgenre_1 != bookgenre_2)

# Birthdays
solver.add(Or(birthday_1 == 'april', birthday_1 == 'sept'))
solver.add(Or(birthday_2 == 'april', birthday_2 == 'sept'))
solver.add(birthday_1 != birthday_2)

# Animals
solver.add(Or(animal_1 == 'horse', animal_1 == 'cat'))
solver.add(Or(animal_2 == 'horse', animal_2 == 'cat'))
solver.add(animal_1 != animal_2)

# Add clues
solver.add(name_1 == 'Eric')  # Clue 1
solver.add(birthday_1 == 'sept')  # Clue 2
solver.add(bookgenre_2 == 'science fiction')  # Clue 3
solver.add(animal_1 == 'horse')  # Clue 4

if solver.check() == sat:
    model = solver.model()
    
    # Extract values for house 1
    h1_name = model.eval(name_1).as_string()
    h1_book = model.eval(bookgenre_1).as_string()
    h1_bday = model.eval(birthday_1).as_string()
    h1_animal = model.eval(animal_1).as_string()
    
    # Extract values for house 2
    h2_name = model.eval(name_2).as_string()
    h2_book = model.eval(bookgenre_2).as_string()
    h2_bday = model.eval(birthday_2).as_string()
    h2_animal = model.eval(animal_2).as_string()
    
    # Create JSON structure
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": [
                ["1", h1_name, h1_book, h1_bday, h1_animal],
                ["2", h2_name, h2_book, h2_bday, h2_animal]
            ]
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")