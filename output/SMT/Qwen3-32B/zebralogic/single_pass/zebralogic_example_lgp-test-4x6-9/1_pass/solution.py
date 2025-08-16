from z3 import *
import json

solver = Solver()

# Variables for each house (0-3)
names = [Int(f"name_{i}") for i in range(4)]
flowers = [Int(f"flower_{i}") for i in range(4)]
heights = [Int(f"height_{i}") for i in range(4)]
mothers = [Int(f"mother_{i}") for i in range(4)]
occupations = [Int(f"occupation_{i}") for i in range(4)]
sports = [Int(f"sport_{i}") for i in range(4)]

# Add distinct constraints
for var in [names, flowers, heights, mothers, occupations, sports]:
    solver.add(Distinct(var))

# Add domain constraints (0-3)
for i in range(4):
    for var in [names[i], flowers[i], heights[i], mothers[i], occupations[i], sports[i]]:
        solver.add(And(0 <= var, var <= 3))

# Clue 6: Teacher is in first house (index 0)
solver.add(occupations[0] == 2)

# Clue 11: Peter is a doctor
for i in range(4):
    solver.add(Implies(names[i] == 0, occupations[i] == 1))

# Clue 13: Arnold loves lilies
for i in range(4):
    solver.add(Implies(names[i] == 1, flowers[i] == 3))

# Clue 3: Arnold is tall
for i in range(4):
    solver.add(Implies(names[i] == 1, heights[i] == 3))

# Clue 12: Mother Aniya is Alice
for i in range(4):
    solver.add(Implies(mothers[i] == 3, names[i] == 3))

# Clue 7: Mother Janelle loves carnations
for i in range(4):
    solver.add(Implies(mothers[i] == 0, flowers[i] == 1))

# Clue 5: Soccer lover is short
for i in range(4):
    solver.add(Implies(sports[i] == 3, heights[i] == 1))

# Clue 8: Basketball lover has average height
for i in range(4):
    solver.add(Implies(sports[i] == 1, heights[i] == 2))

# Clue 9: Arnold not in third house (index 2)
solver.add(names[2] != 1)

# Clue 2: Rose lover is Eric
for i in range(4):
    solver.add(Implies(flowers[i] == 2, names[i] == 2))

# Clue 1: Swimming lover loves roses
for i in range(4):
    solver.add( (sports[i] == 0) == (flowers[i] == 2) )

# Clue 4: Daffodils to the right of engineer
engineer_house = Int('engineer_house')
daffodils_house = Int('daffodils_house')
for i in range(4):
    solver.add(Implies(occupations[i] == 0, engineer_house == i))
    solver.add(Implies(flowers[i] == 0, daffodils_house == i))
solver.add(daffodils_house > engineer_house)

# Clue 10: Holly to the right of average height
holly_house = Int('holly_house')
average_house = Int('average_house')
for i in range(4):
    solver.add(Implies(mothers[i] == 2, holly_house == i))
    solver.add(Implies(heights[i] == 2, average_house == i))
solver.add(holly_house > average_house)

if solver.check() == sat:
    model = solver.model()
    # Prepare the solution
    solution = []
    # Mappings
    names_map = {0: 'Peter', 1: 'Arnold', 2: 'Eric', 3: 'Alice'}
    flowers_map = {0: 'daffodils', 1: 'carnations', 2: 'roses', 3: 'lilies'}
    heights_map = {0: 'very short', 1: 'short', 2: 'average', 3: 'tall'}
    mothers_map = {0: 'Janelle', 1: 'Kailyn', 2: 'Holly', 3: 'Aniya'}
    occupations_map = {0: 'engineer', 1: 'doctor', 2: 'teacher', 3: 'artist'}
    sports_map = {0: 'swimming', 1: 'basketball', 2: 'tennis', 3: 'soccer'}
    
    for i in range(4):
        house_num = i + 1
        name = names_map[model.eval(names[i]).as_long()]
        flower = flowers_map[model.eval(flowers[i]).as_long()]
        height = heights_map[model.eval(heights[i]).as_long()]
        mother = mothers_map[model.eval(mothers[i]).as_long()]
        occupation = occupations_map[model.eval(occupations[i]).as_long()]
        sport = sports_map[model.eval(sports[i]).as_long()]
        solution.append([str(house_num), name, flower, height, mother, occupation, sport])
    
    print(json.dumps({"solution": {"header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"], "rows": solution}}))
else:
    print("No solution found")