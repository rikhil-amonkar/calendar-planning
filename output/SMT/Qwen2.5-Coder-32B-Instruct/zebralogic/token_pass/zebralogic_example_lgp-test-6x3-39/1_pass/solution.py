from z3 import *

# Define the solver
solver = Solver()

# Define variables for each house
names = [Int(f'name_{i}') for i in range(1, 7)]
children = [Int(f'child_{i}') for i in range(1, 7)]
smoothies = [Int(f'smoothie_{i}') for i in range(1, 7)]

# Define the domains for each variable
names_domain = list(range(1, 7))
children_domain = list(range(1, 7))
smoothies_domain = list(range(1, 7))

# Define mappings for names, children, and smoothies
name_map = {1: 'Arnold', 2: 'Peter', 3: 'Carol', 4: 'Alice', 5: 'Bob', 6: 'Eric'}
child_map = {1: 'Alice', 2: 'Timothy', 3: 'Bella', 4: 'Meredith', 5: 'Fred', 6: 'Samantha'}
smoothie_map = {1: 'desert', 2: 'cherry', 3: 'watermelon', 4: 'blueberry', 5: 'lime', 6: 'dragonfruit'}

# Add constraints for each clue
# Clue 1: The person's child is named Fred and the Desert smoothie lover are next to each other.
fred_house = Int('fred_house')
desert_house = Int('desert_house')
solver.add(Or(And(fred_house == desert_house + 1), And(fred_house == desert_house - 1)))
solver.add(children[fred_house - 1] == 5)
solver.add(smoothies[desert_house - 1] == 1)

# Clue 2: The person who drinks Blueberry smoothies is somewhere to the left of the person's child is named Fred.
blueberry_house = Int('blueberry_house')
solver.add(blueberry_house < fred_house)
solver.add(smoothies[blueberry_house - 1] == 4)

# Clue 3: Alice is not in the fifth house.
solver.add(names[4] != 4)

# Clue 4: The person's child is named Samantha is not in the second house.
solver.add(children[1] != 6)

# Clue 5: The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies.
cherry_house = Int('cherry_house')
watermelon_house = Int('watermelon_house')
solver.add(cherry_house < watermelon_house)
solver.add(smoothies[cherry_house - 1] == 3)
solver.add(smoothies[watermelon_house - 1] == 2)

# Clue 6: Alice is the person's child is named Alice.
solver.add(children[3] == 1)

# Clue 7: Alice is the Watermelon smoothie lover.
solver.add(smoothies[3] == 2)

# Clue 8: Peter is somewhere to the right of the person's child is named Samantha.
peter_house = Int('peter_house')
samantha_house = Int('samantha_house')
solver.add(peter_house > samantha_house)
solver.add(children[samantha_house - 1] == 6)
solver.add(names[peter_house - 1] == 2)

# Clue 9: Arnold is not in the second house.
solver.add(names[1] != 1)

# Clue 10: Bob is the person who is the mother of Timothy.
bob_house = Int('bob_house')
timothy_house = Int('timothy_house')
solver.add(bob_house == timothy_house)
solver.add(children[timothy_house - 1] == 2)
solver.add(names[bob_house - 1] == 5)

# Clue 11: Arnold is directly left of Carol.
arnold_house = Int('arnold_house')
carol_house = Int('carol_house')
solver.add(arnold_house == carol_house - 1)
solver.add(names[arnold_house - 1] == 1)
solver.add(names[carol_house - 1] == 3)

# Clue 12: The person who likes Cherry smoothies is directly left of the person's child is named Samantha.
solver.add(cherry_house == samantha_house - 1)

# Clue 13: The person's child is named Meredith is in the sixth house.
solver.add(children[5] == 4)

# Clue 14: The Dragonfruit smoothie lover is the person's child is named Meredith.
solver.add(smoothies[5] == 6)

# Ensure uniqueness of names, children, and smoothies
solver.add(Distinct(names))
solver.add(Distinct(children))
solver.add(Distinct(smoothies))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(1, 7):
        name_val = model.evaluate(names[i - 1]).as_long()
        child_val = model.evaluate(children[i - 1]).as_long()
        smoothie_val = model.evaluate(smoothies[i - 1]).as_long()
        solution.append([str(i), name_map[name_val], child_map[child_val], smoothie_map[smoothie_val]])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Children", "Smoothie"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")