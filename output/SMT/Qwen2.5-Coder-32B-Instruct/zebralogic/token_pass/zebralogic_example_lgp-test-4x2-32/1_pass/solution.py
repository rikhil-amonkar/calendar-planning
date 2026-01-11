from z3 import *

# Define variables
houses = [1, 2, 3, 4]
names = ['Peter', 'Arnold', 'Eric', 'Alice']
pets = ['bird', 'fish', 'dog', 'cat']

# Create dictionaries for the variables
name_vars = {h: Int(f'name_{h}') for h in houses}
pet_vars = {h: Int(f'pet_{h}') for h in houses}

# Create a solver instance
solver = Solver()

# Add constraints for names
for h in houses:
    solver.add(name_vars[h] >= 0)
    solver.add(name_vars[h] <= 3)

# Add constraints for pets
for h in houses:
    solver.add(pet_vars[h] >= 0)
    solver.add(pet_vars[h] <= 3)

# All names and pets must be unique
solver.add(Distinct([name_vars[h] for h in houses]))
solver.add(Distinct([pet_vars[h] for h in houses]))

# Clue 1: The person who owns a dog is somewhere to the right of Alice.
alice_house = Int('alice_house')
dog_house = Int('dog_house')
solver.add(Or([If(name_vars[h] == names.index('Alice'), alice_house == h, True) for h in houses]))
solver.add(Or([If(pet_vars[h] == pets.index('dog'), dog_house == h, True) for h in houses]))
solver.add(dog_house > alice_house)

# Clue 2: Eric is not in the first house.
solver.add(name_vars[1] != names.index('Eric'))

# Clue 3: Eric is the person who keeps a pet bird.
solver.add(Or([If(name_vars[h] == names.index('Eric'), pet_vars[h] == pets.index('bird'), True) for h in houses]))

# Clue 4: There is one house between the person with an aquarium of fish and Peter.
peter_house = Int('peter_house')
fish_house = Int('fish_house')
solver.add(Or([If(name_vars[h] == names.index('Peter'), peter_house == h, True) for h in houses]))
solver.add(Or([If(pet_vars[h] == pets.index('fish'), fish_house == h, True) for h in houses]))
solver.add(Or(peter_house == fish_house + 2, peter_house == fish_house - 2))

# Clue 5: Alice is not in the first house.
solver.add(name_vars[1] != names.index('Alice'))

# Clue 6: Arnold is the person with an aquarium of fish.
solver.add(Or([If(name_vars[h] == names.index('Arnold'), pet_vars[h] == pets.index('fish'), True) for h in houses]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in houses:
        name_index = model[name_vars[h]].as_long()
        pet_index = model[pet_vars[h]].as_long()
        solution.append([str(h), names[name_index], pets[pet_index]])
    
    # Format the solution as a JSON object
    result = {
        "solution": {
            "header": ["House", "Name", "Pet"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")