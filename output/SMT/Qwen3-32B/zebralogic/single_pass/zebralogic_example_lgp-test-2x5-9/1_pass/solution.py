import json
from z3 import *

def solve():
    s = Solver()

    # Variables for house 1 and 2
    name1 = String('name1')
    name2 = String('name2')

    book1 = String('book1')
    book2 = String('book2')

    vacation1 = String('vacation1')
    vacation2 = String('vacation2')

    animal1 = String('animal1')
    animal2 = String('animal2')

    music1 = String('music1')
    music2 = String('music2')

    # Add constraints for uniqueness and possible values
    # Names
    s.add(Or(name1 == 'Arnold', name1 == 'Eric'))
    s.add(Or(name2 == 'Arnold', name2 == 'Eric'))
    s.add(name1 != name2)

    # Book genres
    s.add(Or(book1 == 'science fiction', book1 == 'mystery'))
    s.add(Or(book2 == 'science fiction', book2 == 'mystery'))
    s.add(book1 != book2)

    # Vacations
    s.add(Or(vacation1 == 'mountain', vacation1 == 'beach'))
    s.add(Or(vacation2 == 'mountain', vacation2 == 'beach'))
    s.add(vacation1 != vacation2)

    # Animals
    s.add(Or(animal1 == 'cat', animal1 == 'horse'))
    s.add(Or(animal2 == 'cat', animal2 == 'horse'))
    s.add(animal1 != animal2)

    # Music genres
    s.add(Or(music1 == 'rock', music1 == 'pop'))
    s.add(Or(music2 == 'rock', music2 == 'pop'))
    s.add(music1 != music2)

    # Add clues
    # Clue 5: mystery in house 1
    s.add(book1 == 'mystery')

    # Clue 3: Rock implies mystery
    s.add(Implies(music1 == 'rock', book1 == 'mystery'))
    s.add(Implies(music2 == 'rock', book2 == 'mystery'))

    # Clue 4: animal2 is not cat
    s.add(animal2 != 'cat')

    # Clue 1: beach implies name is Eric
    s.add(Implies(vacation1 == 'beach', name1 == 'Eric'))
    s.add(Implies(vacation2 == 'beach', name2 == 'Eric'))

    # Clue 2: pop iff beach
    s.add((music1 == 'pop') == (vacation1 == 'beach'))
    s.add((music2 == 'pop') == (vacation2 == 'beach'))

    if s.check() == sat:
        model = s.model()
        h1_name = model[name1]
        h1_book = model[book1]
        h1_vacation = model[vacation1]
        h1_animal = model[animal1]
        h1_music = model[music1]

        h2_name = model[name2]
        h2_book = model[book2]
        h2_vacation = model[vacation2]
        h2_animal = model[animal2]
        h2_music = model[music2]

        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                "rows": [
                    ["1", h1_name, h1_book, h1_vacation, h1_animal, h1_music],
                    ["2", h2_name, h2_book, h2_vacation, h2_animal, h2_music]
                ]
            }
        }

        # Convert Z3 string values to Python strings
        for row in solution['solution']['rows']:
            for i in range(1, 6):  # columns 1 to 5 (index 1 to 5)
                row[i] = row[i].as_string()

        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

solve()