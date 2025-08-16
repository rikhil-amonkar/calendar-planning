from z3 import *

# Define the variables
names = ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter']
mothers = ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn']
pets = ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit']

# Create Z3 variables
house_vars = [Int(f'house_{i}') for i in range(1, 7)]
name_vars = {name: Int(f'name_{name}') for name in names}
mother_vars = {mother: Int(f'mother_{mother}') for mother in mothers}
pet_vars = {pet: Int(f'pet_{pet}') for pet in pets}

# Create solver instance
solver = Solver()

# Add constraints for unique assignments
solver.add(Distinct(house_vars))
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(mother_vars.values()))
solver.add(Distinct(pet_vars.values()))

# Map each variable to its corresponding house number
for i in range(6):
    solver.add(house_vars[i] == i + 1)

# Add clues as constraints
# Clue 1: Bob is not in the second house.
solver.add(name_vars['Bob'] != 2)

# Clue 2: There are two houses between the person who has a cat and the person who owns a rabbit.
cat_house = pet_vars['cat']
rabbit_house = pet_vars['rabbit']
solver.add(Abs(cat_house - rabbit_house) == 3)

# Clue 3: The person who has a cat is directly left of The person whose mother's name is Holly.
holly_house = mother_vars['Holly']
solver.add(cat_house + 1 == holly_house)

# Clue 4: The person with a pet hamster is directly left of the person who owns a rabbit.
hamster_house = pet_vars['hamster']
solver.add(hamster_house + 1 == rabbit_house)

# Clue 5: The person who owns a rabbit is Eric.
solver.add(name_vars['Eric'] == rabbit_house)

# Clue 6: There is one house between the person who owns a dog and the person who has a cat.
dog_house = pet_vars['dog']
solver.add(Abs(dog_house - cat_house) == 2)

# Clue 7: The person who has a cat is The person whose mother's name is Janelle.
janelle_house = mother_vars['Janelle']
solver.add(cat_house == janelle_house)

# Clue 8: Alice is directly left of Carol.
alice_house = name_vars['Alice']
carol_house = name_vars['Carol']
solver.add(alice_house + 1 == carol_house)

# Clue 9: Carol is The person whose mother's name is Aniya.
aniya_house = mother_vars['Aniya']
solver.add(carol_house == aniya_house)

# Clue 10: Arnold is the person who has a cat.
arnold_house = name_vars['Arnold']
solver.add(arnold_house == cat_house)

# Clue 11: The person whose mother's name is Kailyn is the person who owns a rabbit.
kailyn_house = mother_vars['Kailyn']
solver.add(kailyn_house == rabbit_house)

# Clue 12: The person with an aquarium of fish is The person whose mother's name is Sarah.
sarah_house = mother_vars['Sarah']
fish_house = pet_vars['fish']
solver.add(sarah_house == fish_house)

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = []
    for house in range(1, 7):
        name = next(n for n, v in name_vars.items() if model[v] == house)
        mother = next(m for m, v in mother_vars.items() if model[v] == house)
        pet = next(p for p, v in pet_vars.items() if model[v] == house)
        solution.append([str(house), name, mother, pet])
    
    # Format the solution as JSON
    json_solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": solution
        }
    }
    print(json_solution)
else:
    print("No solution found")