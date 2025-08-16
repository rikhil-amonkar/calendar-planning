from z3 import *

# Create Solver
solver = Solver()

# Define Variables
names = ['Eric', 'Peter', 'Arnold']
mothers = ['Holly', 'Aniya', 'Janelle']
foods = ['pizza', 'grilled cheese', 'spaghetti']
houses = [1, 2, 3]

# Create symbolic variables
house_name = {h: Int(f'house_name_{h}') for h in houses}
house_mother = {h: Int(f'house_mother_{h}') for h in houses}
house_food = {h: Int(f'house_food_{h}') for h in houses}

# Map indices to values
name_map = {n: i for i, n in enumerate(names)}
mother_map = {m: i for i, m in enumerate(mothers)}
food_map = {f: i for i, f in enumerate(foods)}

# Constraints for unique assignments
solver.add(Distinct([house_name[h] for h in houses]))
solver.add(Distinct([house_mother[h] for h in houses]))
solver.add(Distinct([house_food[h] for h in houses]))

# Clue 1: The person who loves the spaghetti eater and Peter are next to each other.
# If Peter is in house h, then the spaghetti eater is in house h-1 or h+1
for h in houses:
    if h > 1:
        solver.add(Or((house_name[h] == name_map['Peter']) == (house_food[h-1] == food_map['spaghetti']),
                       (house_name[h-1] == name_map['Peter']) == (house_food[h] == food_map['spaghetti'])))
    elif h < 3:
        solver.add((house_name[h] == name_map['Peter']) == (house_food[h+1] == food_map['spaghetti']))

# Clue 2: The person who loves eating grilled cheese is directly left of The person whose mother's name is Aniya.
for h in houses[:-1]:
    solver.add((house_food[h] == food_map['grilled cheese']) == (house_mother[h+1] == mother_map['Aniya']))

# Clue 3: The person who loves eating grilled cheese is Eric.
for h in houses:
    solver.add((house_food[h] == food_map['grilled cheese']) == (house_name[h] == name_map['Eric']))

# Clue 4: Peter is The person whose mother's name is Holly.
for h in houses:
    solver.add((house_name[h] == name_map['Peter']) == (house_mother[h] == mother_map['Holly']))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in houses:
        name_val = names[model[house_name[h]].as_long()]
        mother_val = mothers[model[house_mother[h]].as_long()]
        food_val = foods[model[house_food[h]].as_long()]
        solution.append([str(h), name_val, mother_val, food_val])
    
    # Print the solution in the required format
    print({
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": solution
        }
    })
else:
    print("No solution found")