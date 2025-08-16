import z3
import json

# Initialize Z3 solver
solver = z3.Solver()

# Create variables for each attribute per house (0-based index for 4 houses)
names = [z3.Int(f'Name_{i}') for i in range(4)]
smoothies = [z3.Int(f'Smoothie_{i}') for i in range(4)]
sports = [z3.Int(f'Sport_{i}') for i in range(4)]
cars = [z3.Int(f'Car_{i}') for i in range(4)]
flowers = [z3.Int(f'Flower_{i}') for i in range(4)]

# Add domain constraints (0-3) and uniqueness for each attribute
for attr in [names, smoothies, sports, cars, flowers]:
    for v in attr:
        solver.add(z3.And(0 <= v, v <= 3))
    solver.add(z3.Distinct(attr))

# Add clues as constraints
# Clue 1: Tesla (0) → Roses (1)
for i in range(4):
    solver.add(z3.Implies(cars[i] == 0, flowers[i] == 1))

# Clue 2: Peter (2) → Dragonfruit (0)
for i in range(4):
    solver.add(z3.Implies(names[i] == 2, smoothies[i] == 0))

# Clue 3: Desert (2) → Toyota Camry (1)
for i in range(4):
    solver.add(z3.Implies(smoothies[i] == 2, cars[i] == 1))

# Clue 4: House 1 (index 0) has Tennis (1)
solver.add(sports[0] == 1)

# Clue 5: Toyota Camry (1) next to Basketball (2)
for i in range(4):
    if i == 0:
        solver.add(z3.Implies(cars[i] == 1, sports[1] == 2))
    elif i == 1:
        solver.add(z3.Implies(cars[i] == 1, z3.Or(sports[0] == 2, sports[2] == 2)))
    elif i == 2:
        solver.add(z3.Implies(cars[i] == 1, z3.Or(sports[1] == 2, sports[3] == 2)))
    elif i == 3:
        solver.add(z3.Implies(cars[i] == 1, sports[2] == 2))

# Clue 6: Arnold (3) → Basketball (2)
for i in range(4):
    solver.add(z3.Implies(names[i] == 3, sports[i] == 2))

# Clue 7: Honda Civic (2) → Daffodils (0)
for i in range(4):
    solver.add(z3.Implies(cars[i] == 2, flowers[i] == 0))

# Clue 8: Eric (0) → Roses (1)
for i in range(4):
    solver.add(z3.Implies(names[i] == 0, flowers[i] == 1))

# Clue 9: Watermelon (3) not in house 1 (index 0)
solver.add(smoothies[0] != 3)

# Clue 10: Honda Civic (2) to the right of Desert (2)
for i in range(4):
    for j in range(4):
        solver.add(z3.Implies(z3.And(smoothies[i] == 2, cars[j] == 2), j > i))

# Clue 11: Basketball (2) → Lilies (2)
for i in range(4):
    solver.add(z3.Implies(sports[i] == 2, flowers[i] == 2))

# Clue 12: Tennis (1) and Soccer (0) adjacent
solver.add(z3.Or(
    z3.And(sports[0] == 1, sports[1] == 0),
    z3.And(sports[0] == 0, sports[1] == 1),
    z3.And(sports[1] == 1, sports[2] == 0),
    z3.And(sports[1] == 0, sports[2] == 1),
    z3.And(sports[2] == 1, sports[3] == 0),
    z3.And(sports[2] == 0, sports[3] == 1)
))

# Check if the solver can find a solution
if solver.check() == z3.sat:
    model = solver.model()
    
    # Mappings from indices to actual values
    name_map = {0: 'Eric', 1: 'Alice', 2: 'Peter', 3: 'Arnold'}
    smoothie_map = {0: 'dragonfruit', 1: 'cherry', 2: 'desert', 3: 'watermelon'}
    sport_map = {0: 'soccer', 1: 'tennis', 2: 'basketball', 3: 'swimming'}
    car_map = {0: 'tesla model 3', 1: 'toyota camry', 2: 'honda civic', 3: 'ford f150'}
    flower_map = {0: 'daffodils', 1: 'roses', 2: 'lilies', 3: 'carnations'}
    
    # Build the solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
            "rows": []
        }
    }
    
    for i in range(4):
        house_num = i + 1
        name_idx = model.evaluate(names[i]).as_long()
        smoothie_idx = model.evaluate(smoothies[i]).as_long()
        sport_idx = model.evaluate(sports[i]).as_long()
        car_idx = model.evaluate(cars[i]).as_long()
        flower_idx = model.evaluate(flowers[i]).as_long()
        
        name = name_map[name_idx]
        smoothie = smoothie_map[smoothie_idx]
        sport = sport_map[sport_idx]
        car = car_map[car_idx]
        flower = flower_map[flower_idx]
        
        solution["solution"]["rows"].append([str(house_num), name, smoothie, sport, car, flower])
    
    # Output the solution as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")