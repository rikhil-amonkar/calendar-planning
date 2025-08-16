from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4]

# Attributes
names = ['Peter', 'Eric', 'Alice', 'Arnold']
educations = ['bachelor', 'high school', 'associate', 'master']
music_genres = ['jazz', 'rock', 'pop', 'classical']
colors = ['green', 'red', 'yellow', 'white']
flowers = ['lilies', 'carnations', 'daffodils', 'roses']

# Create variables for each attribute in each house
name = {h: String(f'name_{h}') for h in houses}
education = {h: String(f'education_{h}') for h in houses}
music = {h: String(f'music_{h}') for h in houses}
color = {h: String(f'color_{h}') for h in houses}
flower = {h: String(f'flower_{h}') for h in houses}

# Add constraints that all attributes in each category are distinct for each house
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([education[h] for h in houses]))
s.add(Distinct([music[h] for h in houses]))
s.add(Distinct([color[h] for h in houses]))
s.add(Distinct([flower[h] for h in houses]))

# Each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([education[h] == e for e in educations]))
    s.add(Or([music[h] == m for m in music_genres]))
    s.add(Or([color[h] == c for c in colors]))
    s.add(Or([flower[h] == f for f in flowers]))

# Clue 1: The person with a bachelor's degree is the person who loves a bouquet of daffodils.
for h in houses:
    s.add(Implies(education[h] == 'bachelor', flower[h] == 'daffodils'))

# Clue 2: The person who loves a carnations arrangement is not in the first house.
s.add(flower[1] != 'carnations')

# Clue 3: The person with a master's degree is Alice.
for h in houses:
    s.add(Implies(education[h] == 'master', name[h] == 'Alice'))

# Clue 4: The person with a master's degree is directly left of the person who loves classical music.
for h in range(1, 4):
    s.add(Implies(education[h] == 'master', music[h+1] == 'classical'))
s.add(Or([education[h] == 'master' for h in range(1, 4)]))

# Clue 5: Eric is not in the second house.
s.add(name[2] != 'Eric')

# Clue 6: Arnold is not in the third house.
s.add(name[3] != 'Arnold')

# Clue 7: The person who loves yellow is directly left of the person who loves the rose bouquet.
for h in range(1, 4):
    s.add(Implies(color[h] == 'yellow', flower[h+1] == 'roses'))

# Clue 8: The person who loves pop music is in the second house.
s.add(music[2] == 'pop')

# Clue 9: The person with an associate's degree is not in the fourth house.
s.add(education[4] != 'associate')

# Clue 10: The person who loves a carnations arrangement is not in the fourth house.
s.add(flower[4] != 'carnations')

# Clue 11: The person whose favorite color is red is directly left of the person who loves white.
for h in range(1, 4):
    s.add(Implies(color[h] == 'red', color[h+1] == 'white'))

# Clue 12: The person whose favorite color is red is the person who loves rock music.
for h in houses:
    s.add(Implies(color[h] == 'red', music[h] == 'rock'))

# Clue 13: Arnold is the person who loves yellow.
for h in houses:
    s.add(Implies(name[h] == 'Arnold', color[h] == 'yellow'))

# Clue 14: The person who loves a bouquet of daffodils is the person who loves yellow.
for h in houses:
    s.add(Implies(flower[h] == 'daffodils', color[h] == 'yellow'))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "MusicGenre", "Color", "Flower"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(education[h]).as_string(),
            model.eval(music[h]).as_string(),
            model.eval(color[h]).as_string(),
            model.eval(flower[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")