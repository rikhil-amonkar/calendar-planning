import json
from z3 import *

solver = Solver()

n = 4

# Variables for each house (1-4)
name = [Int(f'name_{i+1}') for i in range(n)]
education = [Int(f'education_{i+1}') for i in range(n)]
music = [Int(f'music_{i+1}') for i in range(n)]
color = [Int(f'color_{i+1}') for i in range(n)]
flower = [Int(f'flower_{i+1}') for i in range(n)]

# Constraints for each attribute to be 0-3 and distinct
for vars in [name, education, music, color, flower]:
    for v in vars:
        solver.add(And(0 <= v, v <= 3))
    solver.add(Distinct(vars))

# Clue 1: Bachelor (0) → daffodils (2)
for i in range(n):
    solver.add(Implies(education[i] == 0, flower[i] == 2))

# Clue 2: Carnations (1) not in house 1
solver.add(flower[0] != 1)

# Clue 3: Master (3) is Alice (2)
for i in range(n):
    solver.add(Implies(education[i] == 3, name[i] == 2))

# Clue 4: Master directly left of classical (music 3)
for i in range(n):
    cond = education[i] == 3
    then = If(i < 3, music[i+1] == 3, False)
    solver.add(Implies(cond, then))

# Clue 5: Eric (1) not in house 2 (index 1)
solver.add(name[1] != 1)

# Clue 6: Arnold (3) not in house 3 (index 2)
solver.add(name[2] != 3)

# Clue 7: Yellow (2) directly left of roses (3)
for i in range(n):
    cond = color[i] == 2
    then = If(i < 3, flower[i+1] == 3, False)
    solver.add(Implies(cond, then))

# Clue 8: Pop (2) in house 2 (index 1)
solver.add(music[1] == 2)

# Clue 9: Associate (2) not in house 4 (index 3)
solver.add(education[3] != 2)

# Clue 10: Carnations (1) not in house 4 (index 3)
solver.add(flower[3] != 1)

# Clue 11: Red (1) directly left of white (3)
for i in range(n):
    cond = color[i] == 1
    then = If(i < 3, color[i+1] == 3, False)
    solver.add(Implies(cond, then))

# Clue 12: Red (1) → rock (1)
for i in range(n):
    solver.add(Implies(color[i] == 1, music[i] == 1))

# Clue 13: Arnold (3) → yellow (2)
for i in range(n):
    solver.add(Implies(name[i] == 3, color[i] == 2))

# Clue 14: Daffodils (2) → yellow (2)
for i in range(n):
    solver.add(Implies(flower[i] == 2, color[i] == 2))

if solver.check() == sat:
    model = solver.model()
    rows = []
    for i in range(n):
        house_num = i + 1
        name_val = model[name[i]].as_long()
        education_val = model[education[i]].as_long()
        music_val = model[music[i]].as_long()
        color_val = model[color[i]].as_long()
        flower_val = model[flower[i]].as_long()
        
        name_str = ["Peter", "Eric", "Alice", "Arnold"][name_val]
        education_str = ["bachelor", "high school", "associate", "master"][education_val]
        music_str = ["jazz", "rock", "pop", "classical"][music_val]
        color_str = ["green", "red", "yellow", "white"][color_val]
        flower_str = ["lilies", "carnations", "daffodils", "roses"][flower_val]
        
        rows.append([str(house_num), name_str, education_str, music_str, color_str, flower_str])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")