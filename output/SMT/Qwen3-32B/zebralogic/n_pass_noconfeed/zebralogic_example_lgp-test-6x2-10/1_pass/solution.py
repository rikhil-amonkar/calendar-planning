from z3 import *
import json

solver = Solver()

# Define EnumSorts for names and music genres
Names, (Arnold, Eric, Peter, Alice, Carol, Bob) = EnumSort('Names', ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob'])
Musics, (jazz, pop, classical, rock, hip_hop, country) = EnumSort('Musics', ['jazz', 'pop', 'classical', 'rock', 'hip_hop', 'country'])

# Create variables for each house (1-6)
names = [Const(f'name_{i}', Names) for i in range(1, 7)]  # indexes 0-5 for houses 1-6
musics = [Const(f'music_{i}', Musics) for i in range(1, 7)]

# All names are distinct
solver.add(Distinct(names))
# All musics are distinct
solver.add(Distinct(musics))

# Clue 3: Carol is in sixth house (index 5)
solver.add(names[5] == Carol)

# Clue 5: Carol loves country music
solver.add(musics[5] == country)

# Clue 9: Hip hop is in third house (index 2)
solver.add(musics[2] == hip_hop)

# Clue 1: Bob is directly left of jazz
solver.add(Or(
    And(names[0] == Bob, musics[1] == jazz),
    And(names[1] == Bob, musics[2] == jazz),
    And(names[2] == Bob, musics[3] == jazz),
    And(names[3] == Bob, musics[4] == jazz),
    And(names[4] == Bob, musics[5] == jazz)
))

# Clue 2: Eric is to the left of hip hop (house 3, so Eric in 1 or 2)
solver.add(Or(names[0] == Eric, names[1] == Eric))

# Clue 4: Eric and hip hop are next to each other (hip hop is in 3, so Eric in 2 or 4)
solver.add(Or(names[1] == Eric, names[3] == Eric))

# Clue 8: The person who loves pop is Peter
for i in range(6):
    solver.add(Implies(musics[i] == pop, names[i] == Peter))

# Clue 10: One house between Peter and Bob
solver.add(Implies(names[0] == Peter, names[2] == Bob))
solver.add(Implies(names[1] == Peter, names[3] == Bob))
solver.add(Implies(names[2] == Peter, Or(names[4] == Bob, names[0] == Bob)))
solver.add(Implies(names[3] == Peter, Or(names[5] == Bob, names[1] == Bob)))
solver.add(Implies(names[4] == Peter, names[2] == Bob))
solver.add(Implies(names[5] == Peter, names[3] == Bob))

# Clue 6: Arnold not in fifth house (index 4)
solver.add(names[4] != Arnold)

# Clue 7: Arnold is to the right of pop (Peter)
for i in range(6):
    if i < 5:
        solver.add(Implies(names[i] == Peter, Or([names[j] == Arnold for j in range(i+1, 6)])))
    else:
        solver.add(Implies(names[i] == Peter, False))  # impossible

# Clue 11: Rock not in fifth house (index 4)
solver.add(musics[4] != rock)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    rows = []
    for i in range(6):
        house_num = i + 1
        name = model.evaluate(names[i]).decl().name()
        music = model.evaluate(musics[i]).decl().name()
        # Replace 'hip_hop' with 'hip hop'
        if music == 'hip_hop':
            music = 'hip hop'
        rows.append([str(house_num), name, music])
    json_output = {
        "solution": {
            "header": ["House", "Name", "MusicGenre"],
            "rows": rows
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")