from z3 import *

# Define the variables
houses = [Int(f'house_{i}') for i in range(1, 5)]
names = ['Peter', 'Arnold', 'Eric', 'Alice']
pets = ['bird', 'fish', 'dog', 'cat']

# Create a solver instance
solver = Solver()

# Add constraints for unique assignment of names and pets to houses
solver.add(Distinct(houses))
solver.add(Or([house == i for house in houses]) for i in range(1, 5))

# Map names and pets to integers for constraint encoding
name_map = {name: Int(name) for name in names}
pet_map = {pet: Int(pet) for pet in pets}

# Ensure each name and pet is assigned to exactly one house
for name in names:
    solver.add(Or([name_map[name] == house for house in houses]))

for pet in pets:
    solver.add(Or([pet_map[pet] == house for house in houses]))

# Add problem-specific constraints
# 1. The person who owns a dog is somewhere to the right of Alice.
for house in houses:
    for h in houses:
        if h < house:
            solver.add(Implies(And(name_map['Alice'] == house, name_map['dog'] == h), False))

# 2. Eric is not in the first house.
solver.add(name_map['Eric'] != 1)

# 3. Eric is the person who keeps a pet bird.
solver.add(name_map['Eric'] == pet_map['bird'])

# 4. There is one house between the person with an aquarium of fish and Peter.
solver.add(Or(name_map['fish'] + 2 == name_map['Peter'], name_map['Peter'] + 2 == name_map['fish']))

# 5. Alice is not in the first house.
solver.add(name_map['Alice'] != 1)

# 6. Arnold is the person with an aquarium of fish.
solver.add(name_map['Arnold'] == pet_map['fish'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {house: {} for house in range(1, 5)}
    for name in names:
        house_number = model.evaluate(name_map[name]).as_long()
        solution[house_number]['Name'] = name
    
    for pet in pets:
        house_number = model.evaluate(pet_map[pet]).as_long()
        solution[house_number]['Pet'] = pet
    
    # Format the solution as required
    result = {
        "solution": {
            "header": ["House", "Name", "Pet"],
            "rows": []
        }
    }
    
    for house in sorted(solution.keys()):
        result["solution"]["rows"].append([str(house), solution[house]["Name"], solution[house]["Pet"]])
    
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")