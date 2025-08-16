from z3 import *
import json

solver = Solver()

# Create variables for each house (1-4)
names = [Int(f'name_{i+1}') for i in range(4)]
hair = [Int(f'hair_{i+1}') for i in range(4)]
music = [Int(f'music_{i+1}') for i in range(4)]

# All variables are between 0 and 3
for h in range(4):
    solver.add(And(0 <= names[h], names[h] <= 3))
    solver.add(And(0 <= hair[h], hair[h] <= 3))
    solver.add(And(0 <= music[h], music[h] <= 3))

# All are distinct
solver.add(Distinct(names))
solver.add(Distinct(hair))
solver.add(Distinct(music))

# Clue 1: Eric (0) has red hair (3) and vice versa
for i in range(4):
    solver.add((names[i] == 0) == (hair[i] == 3))

# Clue 5: classical (3) in first house (house 1, index 0)
solver.add(music[0] == 3)

# Clue 2: classical is directly left of blonde. Since classical is in house 1, house 2 has blonde (hair 0)
solver.add(hair[1] == 0)

# Clue 3: house 1's hair is not brown (2)
solver.add(hair[0] != 2)

# Clue 4: pop (0) not in third house (index 2)
solver.add(music[2] != 0)

# Clue 6: if hair is 3 (red), music is 1 (jazz)
for i in range(4):
    solver.add(Implies(hair[i] == 3, music[i] == 1))

# Clue 7: if music is 2 (rock), name is 1 (Arnold)
for i in range(4):
    solver.add(Implies(music[i] == 2, names[i] == 1))

# Clue 8: Peter (name 2) is to the right of rock music
for i in range(4):
    for j in range(4):
        solver.add(Implies(And(music[i] == 2, names[j] == 2), i < j))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Prepare the solution
    solution = []
    for i in range(4):
        house_num = i + 1
        n = model[names[i]].as_long()
        h = model[hair[i]].as_long()
        m = model[music[i]].as_long()
        # Map to actual names, hair colors, music genres
        name_str = {0: 'Eric', 1: 'Arnold', 2: 'Peter', 3: 'Alice'}[n]
        hair_str = {0: 'blonde', 1: 'black', 2: 'brown', 3: 'red'}[h]
        music_str = {0: 'pop', 1: 'jazz', 2: 'rock', 3: 'classical'}[m]
        solution.append([str(house_num), name_str, hair_str, music_str])
    # Output JSON
    output = {
        "solution": {
            "header": ["House", "Name", "HairColor", "MusicGenre"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")