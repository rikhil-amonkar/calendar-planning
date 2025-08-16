from z3 import *
import json

# Define EnumSorts
Names, (Arnold, Peter, Bob, Eric, Carol, Alice) = EnumSort('Names', ['Arnold', 'Peter', 'Bob', 'Eric', 'Carol', 'Alice'])
Animals, (Horse, Rabbit, Fish, Cat, Bird, Dog) = EnumSort('Animals', ['horse', 'rabbit', 'fish', 'cat', 'bird', 'dog'])
Occupations, (Engineer, Nurse, Lawyer, Teacher, Artist, Doctor) = EnumSort('Occupations', ['engineer', 'nurse', 'lawyer', 'teacher', 'artist', 'doctor'])
Sports, (Basketball, Volleyball, Soccer, Tennis, Baseball, Swimming) = EnumSort('Sports', ['basketball', 'volleyball', 'soccer', 'tennis', 'baseball', 'swimming'])
Heights, (Average, Tall, Short, VeryShort, VeryTall, SuperTall) = EnumSort('Heights', ['average', 'tall', 'short', 'very_short', 'very_tall', 'super_tall'])

# Create variables for each house (0-5)
name = [Const('name_%d' % i, Names) for i in range(6)]
animal = [Const('animal_%d' % i, Animals) for i in range(6)]
occupation = [Const('occupation_%d' % i, Occupations) for i in range(6)]
sport = [Const('sport_%d' % i, Sports) for i in range(6)]
height = [Const('height_%d' % i, Heights) for i in range(6)]

s = Solver()

# Add distinct constraints
s.add(Distinct(name))
s.add(Distinct(animal))
s.add(Distinct(occupation))
s.add(Distinct(sport))
s.add(Distinct(height))

# Add clues as constraints
# Clue 1: Engineer is dog owner
for h in range(6):
    s.add(Implies(occupation[h] == Engineer, animal[h] == Dog))

# Clue 2: Average left of short
for i in range(6):
    for j in range(6):
        if i >= j:
            s.add(Or(height[i] != Average, height[j] != Short))

# Clue 3: Average directly left of rabbit
for h in range(5):  # 0-4
    s.add(Implies(height[h] == Average, animal[h+1] == Rabbit))

# Clue 4: Tall left of very short
for i in range(6):
    for j in range(6):
        if i >= j:
            s.add(Or(height[i] != Tall, height[j] != VeryShort))

# Clue 5: Arnold is cat lover
for h in range(6):
    s.add(Implies(name[h] == Arnold, animal[h] == Cat))

# Clue 6: Horse owner is teacher
for h in range(6):
    s.add(Implies(animal[h] == Horse, occupation[h] == Teacher))

# Clue 7: Carol's sport is soccer
for h in range(6):
    s.add(Implies(name[h] == Carol, sport[h] == Soccer))

# Clue 8: Tall's sport is volleyball
for h in range(6):
    s.add(Implies(height[h] == Tall, sport[h] == Volleyball))

# Clue 9: Lawyer in fifth house (index 4)
s.add(occupation[4] == Lawyer)

# Clue 10: Tennis lover is teacher
for h in range(6):
    s.add(Implies(sport[h] == Tennis, occupation[h] == Teacher))

# Clue 11: Average height loves swimming
for h in range(6):
    s.add(Implies(height[h] == Average, sport[h] == Swimming))

# Clue 12: Baseball directly left of engineer
for h in range(5):
    s.add(Implies(sport[h] == Baseball, occupation[h+1] == Engineer))

# Clue 13: Peter is nurse
for h in range(6):
    s.add(Implies(name[h] == Peter, occupation[h] == Nurse))

# Clue 14: Bob is right of artist
for h1 in range(6):
    for h2 in range(6):
        s.add(Implies(And(name[h1] == Bob, occupation[h2] == Artist), h1 > h2))

# Clue 15: Teacher directly left of soccer
for h in range(5):
    s.add(Implies(occupation[h] == Teacher, sport[h+1] == Soccer))

# Clue 16: Rabbit owner is Alice
for h in range(6):
    s.add(Implies(animal[h] == Rabbit, name[h] == Alice))

# Clue 17: Fish is Carol
for h in range(6):
    s.add(Implies(animal[h] == Fish, name[h] == Carol))

# Clue 18: Baseball in first house (index 0)
s.add(sport[0] == Baseball)

# Clue 19: Cat lover right of very short
for i in range(6):
    for j in range(6):
        if i >= j:
            s.add(Or(height[i] != VeryShort, animal[j] != Cat))

# Clue 20: SuperTall in fifth house (index 4)
s.add(height[4] == SuperTall)

if s.check() == sat:
    model = s.model()
    rows = []
    for i in range(6):
        # Get each value for the house
        n = model[name[i]].decl().name()
        a = model[animal[i]].decl().name()
        o = model[occupation[i]].decl().name()
        sp = model[sport[i]].decl().name()
        h_val = model[height[i]].decl().name().replace('_', ' ')
        rows.append([str(i+1), n, a, o, sp, h_val])
    solution = {
        "solution": {
            "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")