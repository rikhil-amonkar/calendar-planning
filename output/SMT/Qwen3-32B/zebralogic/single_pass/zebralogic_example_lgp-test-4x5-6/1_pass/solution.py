from z3 import *
import json

solver = Solver()

name = [Int(f"name_{i}") for i in range(4)]
education = [Int(f"education_{i}") for i in range(4)]
musicgenre = [Int(f"musicgenre_{i}") for i in range(4)]
color = [Int(f"color_{i}") for i in range(4)]
flower = [Int(f"flower_{i}") for i in range(4)]

for var in [name, education, musicgenre, color, flower]:
    for i in range(4):
        solver.add(0 <= var[i], var[i] < 4)
    solver.add(Distinct(var))

# Clue1: bachelor (0) → flower 2
for i in range(4):
    solver.add(Implies(education[i] == 0, flower[i] == 2))

# Clue2: flower[0] != 1
solver.add(flower[0] != 1)

# Clue3: Alice (name=2) has education=3
for i in range(4):
    solver.add(Implies(name[i] == 2, education[i] == 3))

# Clue4: master (3) directly left of classical (3)
solver.add(Or(*[And(education[i] == 3, musicgenre[i+1] == 3) for i in range(3)]))

# Clue5: name[1] !=1 (Eric not in house 2)
solver.add(name[1] != 1)

# Clue6: name[2] !=3 (Arnold not in house 3)
solver.add(name[2] != 3)

# Clue7: color[i] ==2 → flower[i+1] ==3
for i in range(3):  # i can be 0,1,2
    solver.add(Implies(color[i] == 2, flower[i+1] == 3))

# Clue8: musicgenre[1] ==2 (pop)
solver.add(musicgenre[1] == 2)

# Clue9: education[3] !=2 (associate is 2)
solver.add(education[3] != 2)

# Clue10: flower[3] !=1 (carnations)
solver.add(flower[3] != 1)

# Clue11: color[i] ==1 → color[i+1] ==3
for i in range(3):
    solver.add(Implies(color[i] == 1, color[i+1] == 3))

# Clue12: color[i] ==1 → musicgenre[i] ==1
for i in range(4):
    solver.add(Implies(color[i] == 1, musicgenre[i] == 1))

# Clue13: name[i] ==3 → color[i] ==2
for i in range(4):
    solver.add(Implies(name[i] == 3, color[i] == 2))

# Clue14: flower[i] ==2 → color[i] ==2
for i in range(4):
    solver.add(Implies(flower[i] == 2, color[i] == 2))

if solver.check() == sat:
    model = solver.model()
    # Now process the model
    # For each house 0-3, get the values
    solution = []
    for i in range(4):
        house_num = i + 1
        n = model[name[i]].as_long()
        e = model[education[i]].as_long()
        m = model[musicgenre[i]].as_long()
        c = model[color[i]].as_long()
        f = model[flower[i]].as_long()
        # Map to strings
        name_str = ["Peter", "Eric", "Alice", "Arnold"][n]
        education_str = ["bachelor", "high school", "associate", "master"][e]
        music_str = ["jazz", "rock", "pop", "classical"][m]
        color_str = ["green", "red", "yellow", "white"][c]
        flower_str = ["lilies", "carnations", "daffodils", "roses"][f]
        solution.append([str(house_num), name_str, education_str, music_str, color_str, flower_str])
    # Now create the JSON
    json_output = {
        "solution": {
            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
            "rows": solution
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found")