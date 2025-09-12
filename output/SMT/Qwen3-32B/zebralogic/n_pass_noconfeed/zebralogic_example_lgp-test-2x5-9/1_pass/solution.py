from z3 import *
import json

solver = Solver()

# Variables for house 1
name1 = String('name1')
book1 = String('book1')
vacation1 = String('vacation1')
animal1 = String('animal1')
music1 = String('music1')

# Variables for house 2
name2 = String('name2')
book2 = String('book2')
vacation2 = String('vacation2')
animal2 = String('animal2')
music2 = String('music2')

# Constraints for uniqueness and domain for each category

# Names
solver.add(Or(name1 == "Arnold", name1 == "Eric"))
solver.add(Or(name2 == "Arnold", name2 == "Eric"))
solver.add(name1 != name2)

# Book genres
solver.add(Or(book1 == "science fiction", book1 == "mystery"))
solver.add(Or(book2 == "science fiction", book2 == "mystery"))
solver.add(book1 != book2)

# Vacation
solver.add(Or(vacation1 == "mountain", vacation1 == "beach"))
solver.add(Or(vacation2 == "mountain", vacation2 == "beach"))
solver.add(vacation1 != vacation2)

# Animal
solver.add(Or(animal1 == "cat", animal1 == "horse"))
solver.add(Or(animal2 == "cat", animal2 == "horse"))
solver.add(animal1 != animal2)

# Music
solver.add(Or(music1 == "rock", music1 == "pop"))
solver.add(Or(music2 == "rock", music2 == "pop"))
solver.add(music1 != music2)

# Clue 5: mystery book in first house
solver.add(book1 == "mystery")

# Clue 4: cat lover not in second house
solver.add(animal1 == "cat")

# Clue 1: beach vacation is Eric
solver.add(Implies(vacation1 == "beach", name1 == "Eric"))
solver.add(Implies(vacation2 == "beach", name2 == "Eric"))

# Clue 2: pop music is same as beach vacation
solver.add(Implies(vacation1 == "beach", music1 == "pop"))
solver.add(Implies(vacation2 == "beach", music2 == "pop"))

# Clue 3: rock implies mystery book
solver.add(Implies(music1 == "rock", book1 == "mystery"))
solver.add(Implies(music2 == "rock", book2 == "mystery"))

if solver.check() == sat:
    model = solver.model()
    
    # Extract values for house 1
    h1_name = model.eval(name1).as_string()
    h1_book = model.eval(book1).as_string()
    h1_vacation = model.eval(vacation1).as_string()
    h1_animal = model.eval(animal1).as_string()
    h1_music = model.eval(music1).as_string()
    
    # Extract values for house 2
    h2_name = model.eval(name2).as_string()
    h2_book = model.eval(book2).as_string()
    h2_vacation = model.eval(vacation2).as_string()
    h2_animal = model.eval(animal2).as_string()
    h2_music = model.eval(music2).as_string()
    
    # Build the JSON structure
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": [
                ["1", h1_name, h1_book, h1_vacation, h1_animal, h1_music],
                ["2", h2_name, h2_book, h2_vacation, h2_animal, h2_music]
            ]
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")