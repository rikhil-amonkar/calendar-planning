import json
from z3 import *

# Initialize the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4]

# Define the attributes
names = ['Peter', 'Arnold', 'Eric', 'Alice']
flowers = ['daffodils', 'carnations', 'roses', 'lilies']
heights = ['very short', 'short', 'tall', 'average']
mothers = ['Janelle', 'Kailyn', 'Holly', 'Aniya']
occupations = ['engineer', 'doctor', 'teacher', 'artist']
sports = ['swimming', 'basketball', 'tennis', 'soccer']

# Create variables for each attribute in each house
name = {h: String(f'name_{h}') for h in houses}
flower = {h: String(f'flower_{h}') for h in houses}
height = {h: String(f'height_{h}') for h in houses}
mother = {h: String(f'mother_{h}') for h in houses}
occupation = {h: String(f'occupation_{h}') for h in houses}
sport = {h: String(f'sport_{h}') for h in houses}

# Add constraints that each attribute in each house is one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([flower[h] == f for f in flowers]))
    s.add(Or([height[h] == ht for ht in heights]))
    s.add(Or([mother[h] == m for m in mothers]))
    s.add(Or([occupation[h] == o for o in occupations]))
    s.add(Or([sport[h] == sp for sp in sports]))

# Add uniqueness constraints for each attribute across houses
for attr in [name, flower, height, mother, occupation, sport]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Clue 1: The person who loves swimming is the person who loves the rose bouquet.
for h in houses:
    s.add(Implies(sport[h] == 'swimming', flower[h] == 'roses'))

# Clue 2: The person who loves the rose bouquet is Eric.
for h in houses:
    s.add(Implies(flower[h] == 'roses', name[h] == 'Eric'))

# Clue 3: Arnold is the person who is tall.
for h in houses:
    s.add(Implies(name[h] == 'Arnold', height[h] == 'tall'))

# Clue 4: The person who loves a bouquet of daffodils is somewhere to the right of the person who is an engineer.
# Meaning, the engineer is in a house with a lower number than the house with daffodils.
engineer_house = Int('engineer_house')
daffodils_house = Int('daffodils_house')
s.add(And([Or([And(occupation[h] == 'engineer', engineer_house == h) for h in houses]),
       Or([And(flower[h] == 'daffodils', daffodils_house == h) for h in houses]))
s.add(engineer_house < daffodils_house)

# Clue 5: The person who loves soccer is the person who is short.
for h in houses:
    s.add(Implies(sport[h] == 'soccer', height[h] == 'short'))

# Clue 6: The person who is a teacher is in the first house.
s.add(occupation[1] == 'teacher')

# Clue 7: The person whose mother's name is Janelle is the person who loves a carnations arrangement.
for h in houses:
    s.add(Implies(mother[h] == 'Janelle', flower[h] == 'carnations'))

# Clue 8: The person who loves basketball is the person who has an average height.
for h in houses:
    s.add(Implies(sport[h] == 'basketball', height[h] == 'average'))

# Clue 9: Arnold is not in the third house.
s.add(name[3] != 'Arnold')

# Clue 10: The person whose mother's name is Holly is somewhere to the right of the person who has an average height.
# So average height is in a house with number less than the house where mother is Holly.
average_height_house = Int('average_height_house')
holly_mother_house = Int('holly_mother_house')
s.add(And([Or([And(height[h] == 'average', average_height_house == h) for h in houses]),
       Or([And(mother[h] == 'Holly', holly_mother_house == h) for h in houses]))
s.add(average_height_house < holly_mother_house)

# Clue 11: Peter is the person who is a doctor.
for h in houses:
    s.add(Implies(name[h] == 'Peter', occupation[h] == 'doctor'))

# Clue 12: The person whose mother's name is Aniya is Alice.
for h in houses:
    s.add(Implies(mother[h] == 'Aniya', name[h] == 'Alice'))

# Clue 13: Arnold is the person who loves the bouquet of lilies.
for h in houses:
    s.add(Implies(name[h] == 'Arnold', flower[h] == 'lilies'))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
            "rows": []
        }
    }
    
    for h in houses:
        row = [
            str(h),
            str(model.eval(name[h])),
            str(model.eval(flower[h])),
            str(model.eval(height[h])),
            str(model.eval(mother[h])),
            str(model.eval(occupation[h])),
            str(model.eval(sport[h]))
        ]
        solution["solution"]["rows"].append(row)
    
    # Convert to JSON
    json_output = json.dumps(solution, indent=2)
    print(json_output)
else:
    print("No solution found")