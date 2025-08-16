from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
names = ['Alice', 'Peter', 'Arnold', 'Eric']
mothers = ['Holly', 'Kailyn', 'Janelle', 'Aniya']
flowers = ['carnations', 'roses', 'lilies', 'daffodils']
houses = [1, 2, 3, 4]

# Declare variables for each house
house_name = {h: Int(f'house_name_{h}') for h in houses}
house_mother = {h: Int(f'house_mother_{h}') for h in houses}
house_flower = {h: Int(f'house_flower_{h}') for h in houses}

# Add constraints for unique values within each category
solver.add(Distinct([house_name[h] for h in houses]))
solver.add(Distinct([house_mother[h] for h in houses]))
solver.add(Distinct([house_flower[h] for h in houses]))

# Map indices to actual values
name_map = {i: names[i] for i in range(len(names))}
mother_map = {i: mothers[i] for i in range(len(mothers))}
flower_map = {i: flowers[i] for i in range(len(flowers))}

# Add clues as constraints
# Clue 1: Alice is The person whose mother's name is Kailyn.
solver.add(house_name[3] == names.index('Alice'))
solver.add(house_mother[3] == mothers.index('Kailyn'))

# Clue 2: The person whose mother's name is Janelle is somewhere to the right of Arnold.
janelle_house = Int('janelle_house')
arnold_house = Int('arnold_house')
solver.add(janelle_house == house_mother.index(mothers.index('Janelle')))
solver.add(arnold_house == house_mother.index(mothers.index('Holly')))
solver.add(janelle_house > arnold_house)

# Clue 3: Peter is somewhere to the right of the person who loves a carnations arrangement.
carnations_house = Int('carnations_house')
peter_house = Int('peter_house')
solver.add(carnations_house == house_flower.index(flowers.index('carnations')))
solver.add(peter_house == house_name.index(names.index('Peter')))
solver.add(peter_house > carnations_house)

# Clue 4: Eric is the person who loves a bouquet of daffodils.
solver.add(house_name[house_flower.index(flowers.index('daffodils'))] == names.index('Eric'))

# Clue 5: Arnold is The person whose mother's name is Holly.
solver.add(house_name[house_mother.index(mothers.index('Holly'))] == names.index('Arnold'))

# Clue 6: The person who loves a carnations arrangement is somewhere to the right of The person whose mother's name is Holly.
solver.add(carnations_house > arnold_house)

# Clue 7: The person who loves the boquet of lilies is directly left of Alice.
solver.add(house_flower[2] == flowers.index('lilies'))

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in houses:
        name_idx = model[house_name[h]].as_long()
        mother_idx = model[house_mother[h]].as_long()
        flower_idx = model[house_flower[h]].as_long()
        solution.append([str(h), name_map[name_idx], mother_map[mother_idx], flower_map[flower_idx]])
    
    print({
        "solution": {
            "header": ["House", "Name", "Mother", "Flower"],
            "rows": solution
        }
    })
else:
    print("No solution found")