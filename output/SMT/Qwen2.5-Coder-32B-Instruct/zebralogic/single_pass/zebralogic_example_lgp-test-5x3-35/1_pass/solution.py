from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [Int(f'house_{i}') for i in range(1, 6)]
names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
heights = ['average', 'very short', 'short', 'very tall', 'tall']

# Maps for constraints
name_map = {name: Int(f'name_{name}') for name in names}
mother_map = {mother: Int(f'mother_{mother}') for mother in mothers}
height_map = {height: Int(f'height_{height}') for height in heights}

# Each variable must be between 1 and 5
for var in list(name_map.values()) + list(mother_map.values()) + list(height_map.values()):
    solver.add(var >= 1)
    solver.add(var <= 5)

# All variables must be distinct
solver.add(Distinct(list(name_map.values())))
solver.add(Distinct(list(mother_map.values())))
solver.add(Distinct(list(height_map.values())))

# Clue 1: Alice is The person whose mother's name is Aniya.
solver.add(name_map['Alice'] == mother_map['Aniya'])

# Clue 2: The person who has an average height is somewhere to the left of The person whose mother's name is Penny.
solver.add(height_map['average'] < mother_map['Penny'])

# Clue 3: The person whose mother's name is Janelle is Bob.
solver.add(mother_map['Janelle'] == name_map['Bob'])

# Clue 4: Peter is not in the second house.
solver.add(name_map['Peter'] != 2)

# Clue 5: The person who is short is directly left of Arnold.
solver.add(height_map['short'] + 1 == name_map['Arnold'])

# Clue 6: The person who is very tall is Arnold.
solver.add(height_map['very tall'] == name_map['Arnold'])

# Clue 7: Bob is directly left of the person who has an average height.
solver.add(name_map['Bob'] + 1 == height_map['average'])

# Clue 8: Eric is not in the fifth house.
solver.add(name_map['Eric'] != 5)

# Clue 9: The person who is very tall is somewhere to the right of The person whose mother's name is Holly.
solver.add(height_map['very tall'] > mother_map['Holly'])

# Clue 10: Eric is The person whose mother's name is Kailyn.
solver.add(name_map['Eric'] == mother_map['Kailyn'])

# Clue 11: The person who is very short is in the fifth house.
solver.add(height_map['very short'] == 5)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": []
        }
    }
    for house in range(1, 6):
        name = next(name for name, var in name_map.items() if model.evaluate(var) == house).as_string()[1:-1]
        mother = next(mother for mother, var in mother_map.items() if model.evaluate(var) == house).as_string()[1:-1]
        height = next(height for height, var in height_map.items() if model.evaluate(var) == house).as_string()[1:-1]
        solution["solution"]["rows"].append([str(house), name, mother, height])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")