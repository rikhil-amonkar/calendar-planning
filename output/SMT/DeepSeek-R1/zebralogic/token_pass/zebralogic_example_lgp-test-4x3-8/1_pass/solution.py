import json
from z3 import *

def main():
    # Create the solver
    solver = Solver()

    # Define the attributes
    names = ['Eric', 'Arnold', 'Peter', 'Alice']
    hair_colors = ['blonde', 'black', 'brown', 'red']
    music_genres = ['pop', 'jazz', 'rock', 'classical']

    # Create enumerations for each attribute type
    Name = EnumSort('Name', names)
    HairColor = EnumSort('HairColor', hair_colors)
    MusicGenre = EnumSort('MusicGenre', music_genres)

    # Create variables for each house's attributes
    n = [Const(f'n{i}', Name) for i in range(1,5)]
    h = [Const(f'h{i}', HairColor) for i in range(1,5)]
    m = [Const(f'm{i}', MusicGenre) for i in range(1,5)]

    # Add constraint: all attributes are distinct
    solver.add(Distinct(n))
    solver.add(Distinct(h))
    solver.add(Distinct(m))

    # Extract individual constants for easier reference
    Eric, Arnold, Peter, Alice = [Const(name, Name) for name in names]
    blonde, black, brown, red = [Const(color, HairColor) for color in hair_colors]
    pop, jazz, rock, classical = [Const(genre, MusicGenre) for genre in music_genres]

    # Clue 1: Eric has red hair
    for i in range(4):
        solver.add(Implies(n[i] == Eric, h[i] == red))

    # Clue 2: Classical music directly left of blonde hair
    for i in range(3):
        solver.add(Implies(m[i] == classical, h[i+1] == blonde))
    solver.add(Not(Or([And(m[i] == classical, h[i+1] != blonde) for i in range(3)])))

    # Clue 3: Brown hair not in first house
    solver.add(h[0] != brown)

    # Clue 4: Pop music not in third house
    solver.add(m[2] != pop)

    # Clue 5: Classical music in first house
    solver.add(m[0] == classical)

    # Clue 6: Jazz music has red hair
    for i in range(4):
        solver.add(Implies(m[i] == jazz, h[i] == red))

    # Clue 7: Rock music is Arnold
    for i in range(4):
        solver.add(Implies(m[i] == rock, n[i] == Arnold))

    # Clue 8: Peter is right of rock music lover
    rock_pos = Int('rock_pos')
    solver.add(rock_pos >= 1, rock_pos <= 4)
    peter_pos = Int('peter_pos')
    solver.add(peter_pos >= 1, peter_pos <= 4)
    for i in range(4):
        solver.add(If(m[i] == rock, rock_pos == i+1, True))
        solver.add(If(n[i] == Peter, peter_pos == i+1, True))
    solver.add(peter_pos > rock_pos)

    # Check if satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare result data
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = str(model.eval(n[i]))
            hair_val = str(model.eval(h[i]))
            music_val = str(model.eval(m[i]))
            rows.append([house_num, name_val, hair_val, music_val])
        
        result = {
            "solution": {
                "header": ["House", "Name", "HairColor", "MusicGenre"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()