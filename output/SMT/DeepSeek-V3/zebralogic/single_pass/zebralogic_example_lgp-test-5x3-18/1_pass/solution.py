from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define variables for each attribute
names = {house: Const(f'name_{house}', StringSort()) for house in houses}
flowers = {house: Const(f'flower_{house}', StringSort()) for house in houses}
animals = {house: Const(f'animal_{house}', StringSort()) for house in houses}

# All possible values for each attribute
all_names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
all_flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
all_animals = ["dog", "horse", "cat", "bird", "fish"]

# Add constraints for uniqueness
for house in houses:
    s.add(Or([names[house] == StringVal(name) for name in all_names]))
    s.add(Or([flowers[house] == StringVal(flower) for flower in all_flowers]))
    s.add(Or([animals[house] == StringVal(animal) for animal in all_animals]))

for i in range(len(houses)):
    for j in range(i + 1, len(houses)):
        s.add(names[houses[i]] != names[houses[j]])
        s.add(flowers[houses[i]] != flowers[houses[j]])
        s.add(animals[houses[i]] != animals[houses[j]])

# Add constraints based on the clues
# 1. Alice is in the second house.
s.add(names[2] == StringVal("Alice"))

# 2. The person who loves the bouquet of lilies is the bird keeper.
for house in houses:
    s.add(Implies(flowers[house] == StringVal("lilies"), animals[house] == StringVal("bird")))

# 3. Peter is somewhere to the right of the person who loves the vase of tulips.
# Find the house with tulips and ensure Peter is to its right
tulips_house = Const('tulips_house', IntSort())
s.add(Or([And(flowers[house] == StringVal("tulips"), tulips_house == house) for house in houses]))
peter_house = Const('peter_house', IntSort())
s.add(Or([And(names[house] == StringVal("Peter"), peter_house == house) for house in houses]))
s.add(peter_house > tulips_house)

# 4. The fish enthusiast is the person who loves a bouquet of daffodils.
for house in houses:
    s.add(Implies(animals[house] == StringVal("fish"), flowers[house] == StringVal("daffodils")))

# 5. The person who keeps horses is Eric.
for house in houses:
    s.add(Implies(animals[house] == StringVal("horse"), names[house] == StringVal("Eric")))

# 6. There are two houses between the dog owner and Bob.
# Find the dog owner and Bob's house, and ensure there are two houses between them
dog_house = Const('dog_house', IntSort())
s.add(Or([And(animals[house] == StringVal("dog"), dog_house == house) for house in houses]))
bob_house = Const('bob_house', IntSort())
s.add(Or([And(names[house] == StringVal("Bob"), bob_house == house) for house in houses]))
s.add(Or(bob_house == dog_house + 3, dog_house == bob_house + 3))

# 7. The fish enthusiast is directly left of Bob.
# Fish house is immediately to the left of Bob's house
for house in houses:
    if house < 5:
        s.add(Implies(animals[house] == StringVal("fish"), names[house + 1] == StringVal("Bob")))

# 8. Alice is directly left of the person who keeps horses.
# Alice's house is immediately to the left of the horse keeper's house
s.add(Or([And(names[house] == StringVal("Alice"), animals[house + 1] == StringVal("horse")) for house in houses if house < 5]))

# 9. The person who loves carnations is directly left of the person who loves tulips.
# Carnations house is immediately to the left of tulips house
for house in houses:
    if house < 5:
        s.add(Implies(flowers[house] == StringVal("carnations"), flowers[house + 1] == StringVal("tulips")))

# 10. The cat lover is not in the first house.
s.add(animals[1] != StringVal("cat"))

# Solve the model
if s.check() == sat:
    m = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Flower", "Animal"],
            "rows": []
        }
    }
    
    for house in houses:
        name = m.evaluate(names[house])
        flower = m.evaluate(flowers[house])
        animal = m.evaluate(animals[house])
        solution["solution"]["rows"].append([str(house), str(name), str(flower), str(animal)])
    
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")