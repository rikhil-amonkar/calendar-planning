from z3 import *
import json

solver = Solver()

# Create variables for each house (1-4)
name = [Int(f"name_{i}") for i in range(1, 5)]
mother = [Int(f"mother_{i}") for i in range(1, 5)]
flower = [Int(f"flower_{i}") for i in range(1, 5)]

# Each attribute must be 0-3 and distinct
for i in range(1, 5):
    solver.add(And(0 <= name[i], name[i] < 4))
    solver.add(And(0 <= mother[i], mother[i] < 4))
    solver.add(And(0 <= flower[i], flower[i] < 4))

solver.add(Distinct(name[1], name[2], name[3], name[4]))
solver.add(Distinct(mother[1], mother[2], mother[3], mother[4]))
solver.add(Distinct(flower[1], flower[2], flower[3], flower[4]))

# Clue 8: Alice (0) is in house 3
solver.add(name[3] == 0)

# Clue 1: Alice's mother is Kailyn (1)
for i in range(1, 5):
    solver.add(Implies(name[i] == 0, mother[i] == 1))

# Clue 5: Arnold (2) has mother Holly (0)
for i in range(1, 5):
    solver.add(Implies(name[i] == 2, mother[i] == 0))

# Clue 4: Eric (3) has flower daffodils (3)
for i in range(1, 5):
    solver.add(Implies(name[i] == 3, flower[i] == 3))

# Clue 7: flower[2] is lilies (2)
solver.add(flower[2] == 2)

# Clue 2: Janelle (2) is to the right of Arnold
arnold_house = Int('arnold_house')
janelle_house = Int('janelle_house')

constraint_arnold = Or([And(name[i] == 2, arnold_house == i) for i in range(1, 5)])
solver.add(constraint_arnold)
solver.add(And(1 <= arnold_house, arnold_house <= 4))

constraint_janelle = Or([And(mother[i] == 2, janelle_house == i) for i in range(1, 5)])
solver.add(constraint_janelle)
solver.add(And(1 <= janelle_house, janelle_house <= 4))

solver.add(janelle_house > arnold_house)

# Clue 3: Peter (1) is to the right of carnations (0)
carnations_house = Int('carnations_house')
peter_house = Int('peter_house')

constraint_carnations = Or([And(flower[i] == 0, carnations_house == i) for i in range(1, 5)])
solver.add(constraint_carnations)
solver.add(And(1 <= carnations_house, carnations_house <= 4))

constraint_peter = Or([And(name[i] == 1, peter_house == i) for i in range(1, 5)])
solver.add(constraint_peter)
solver.add(And(1 <= peter_house, peter_house <= 4))

solver.add(peter_house > carnations_house)

# Clue 6: carnations_house is to the right of Holly (mother 0)
holly_house = Int('holly_house')
constraint_holly = Or([And(mother[i] == 0, holly_house == i) for i in range(1, 5)])
solver.add(constraint_holly)
solver.add(And(1 <= holly_house, holly_house <= 4))

solver.add(carnations_house > holly_house)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Now extract the values for each house
    solution_rows = []
    name_map = {0: 'Alice', 1: 'Peter', 2: 'Arnold', 3: 'Eric'}
    mother_map = {0: 'Holly', 1: 'Kailyn', 2: 'Janelle', 3: 'Aniya'}
    flower_map = {0: 'carnations', 1: 'roses', 2: 'lilies', 3: 'daffodils'}

    for house in range(1, 5):
        n = model[name[house]].as_long()
        m = model[mother[house]].as_long()
        f = model[flower[house]].as_long()
        solution_rows.append([str(house), name_map[n], mother_map[m], flower_map[f]])

    # Output JSON
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Flower"],
            "rows": solution_rows
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")