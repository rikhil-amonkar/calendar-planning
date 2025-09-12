import z3
import json

solver = z3.Solver()

# Create variables for each house (0-3)
names = [z3.String(f'name_{i}') for i in range(4)]
smoothie = [z3.String(f'smoothie_{i}') for i in range(4)]
sport = [z3.String(f'sport_{i}') for i in range(4)]
car = [z3.String(f'car_{i}') for i in range(4)]
flower = [z3.String(f'flower_{i}') for i in range(4)]

# Add domain constraints for each attribute
name_domain = ['Eric', 'Alice', 'Peter', 'Arnold']
smoothie_domain = ['dragonfruit', 'cherry', 'desert', 'watermelon']
sport_domain = ['soccer', 'tennis', 'basketball', 'swimming']
car_domain = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
flower_domain = ['daffodils', 'roses', 'lilies', 'carnations']

for i in range(4):
    solver.add(z3.Or([names[i] == name for name in name_domain]))
    solver.add(z3.Or([smoothie[i] == s for s in smoothie_domain]))
    solver.add(z3.Or([sport[i] == sp for sp in sport_domain]))
    solver.add(z3.Or([car[i] == c for c in car_domain]))
    solver.add(z3.Or([flower[i] == f for f in flower_domain]))

# Add uniqueness constraints for each attribute
for attr in [names, smoothie, sport, car, flower]:
    solver.add(z3.Distinct(*attr))

# Now add the clues as constraints.

# Clue 2: Peter is Dragonfruit smoothie lover
for i in range(4):
    solver.add(z3.Implies(names[i] == 'Peter', smoothie[i] == 'dragonfruit'))

# Clue 3: Desert smoothie lover owns Toyota Camry
for i in range(4):
    solver.add(z3.Implies(smoothie[i] == 'desert', car[i] == 'toyota camry'))

# Clue 4: Tennis lover in first house (index 0)
solver.add(sport[0] == 'tennis')

# Clue 5: Toyota Camry and basketball lover are adjacent
for i in range(4):
    for j in range(4):
        solver.add(z3.Implies(z3.And(car[i] == 'toyota camry', sport[j] == 'basketball'), z3.Abs(i - j) == 1))

# Clue 6: Arnold loves basketball
for i in range(4):
    solver.add(z3.Implies(names[i] == 'Arnold', sport[i] == 'basketball'))

# Clue 7: Honda Civic owner loves daffodils
for i in range(4):
    solver.add(z3.Implies(car[i] == 'honda civic', flower[i] == 'daffodils'))

# Clue 8: Eric loves roses
for i in range(4):
    solver.add(z3.Implies(names[i] == 'Eric', flower[i] == 'roses'))

# Clue 1: Tesla Model 3 owner loves roses
for i in range(4):
    solver.add(z3.Implies(car[i] == 'tesla model 3', flower[i] == 'roses'))

# Clue 9: Watermelon not in first house
solver.add(smoothie[0] != 'watermelon')

# Clue 10: Honda Civic is to the right of Desert smoothie lover
for i in range(4):
    for j in range(4):
        solver.add(z3.Implies(z3.And(smoothie[i] == 'desert', car[j] == 'honda civic'), i < j))

# Clue 11: Basketball lover loves lilies
for i in range(4):
    solver.add(z3.Implies(sport[i] == 'basketball', flower[i] == 'lilies'))

# Clue 12: Tennis and Soccer lovers are adjacent
for i in range(4):
    for j in range(4):
        solver.add(z3.Implies(z3.And(sport[i] == 'tennis', sport[j] == 'soccer'), z3.Abs(i - j) == 1))

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Now extract the assignments
    # For each house, collect the values
    solution = []
    for i in range(4):
        house_num = i + 1
        name = model.evaluate(names[i]).as_string()
        s = model.evaluate(smoothie[i]).as_string()
        sp = model.evaluate(sport[i]).as_string()
        c = model.evaluate(car[i]).as_string()
        f = model.evaluate(flower[i]).as_string()
        solution.append([str(house_num), name, s, sp, c, f])
    # Now output as JSON
    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")