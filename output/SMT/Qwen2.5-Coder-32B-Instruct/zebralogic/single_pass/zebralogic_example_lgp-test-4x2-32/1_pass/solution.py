from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each house
house_names = [Int(f"house_{i}_name") for i in range(1, 5)]
house_pets = [Int(f"house_{i}_pet") for i in range(1, 5)]

# Define the domains for names and pets
names = {"Peter": 1, "Arnold": 2, "Eric": 3, "Alice": 4}
pets = {"bird": 1, "fish": 2, "dog": 3, "cat": 4}

# Add constraints for unique names and pets per house
solver.add(Distinct(house_names))
solver.add(Distinct(house_pets))

# Clue 1: The person who owns a dog is somewhere to the right of Alice.
alice_house = Int('alice_house')
dog_house = Int('dog_house')
solver.add(Or([And(house_names[i] == names["Alice"], alice_house == i + 1) for i in range(4)]))
solver.add(Or([And(house_pets[i] == pets["dog"], dog_house == i + 1) for i in range(4)]))
solver.add(dog_house > alice_house)

# Clue 2: Eric is not in the first house.
solver.add(house_names[0] != names["Eric"])

# Clue 3: Eric is the person who keeps a pet bird.
solver.add(Or([And(house_names[i] == names["Eric"], house_pets[i] == pets["bird"]) for i in range(4)]))

# Clue 4: There is one house between the person with an aquarium of fish and Peter.
peter_house = Int('peter_house')
fish_house = Int('fish_house')
solver.add(Or([And(house_names[i] == names["Peter"], peter_house == i + 1) for i in range(4)]))
solver.add(Or([And(house_pets[i] == pets["fish"], fish_house == i + 1) for i in range(4)]))
solver.add(Or(fish_house == peter_house - 2, fish_house == peter_house + 2))

# Clue 5: Alice is not in the first house.
solver.add(house_names[0] != names["Alice"])

# Clue 6: Arnold is the person with an aquarium of fish.
solver.add(Or([And(house_names[i] == names["Arnold"], house_pets[i] == pets["fish"]) for i in range(4)]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Pet"],
            "rows": []
        }
    }
    for i in range(4):
        house_number = str(i + 1)
        name = [k for k, v in names.items() if v == model[house_names[i]].as_long()][0]
        pet = [k for k, v in pets.items() if v == model[house_pets[i]].as_long()][0]
        solution["solution"]["rows"].append([house_number, name, pet])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")