from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = range(1, 7)
names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]

# Declare variables for each house
house_name = {h: String('house_name_%d' % h) for h in houses}
house_child = {h: String('house_child_%d' % h) for h in houses}
house_smoothie = {h: String('house_smoothie_%d' % h) for h in houses}

# Add constraints for unique assignments
solver.add(Distinct([house_name[h] for h in houses]))
solver.add(Distinct([house_child[h] for h in houses]))
solver.add(Distinct([house_smoothie[h] for h in houses]))

# Add specific constraints based on clues
# Clue 1: The person's child is named Fred and the Desert smoothie lover are next to each other.
for h in range(1, 6):
    solver.add(Or(And(house_child[h] == "Fred", house_smoothie[h+1] == "desert"),
                 And(house_child[h+1] == "Fred", house_smoothie[h] == "desert")))

# Clue 2: The person who drinks Blueberry smoothies is somewhere to the left of the person's child is named Fred.
for h in range(1, 6):
    solver.add(Implies(house_smoothie[h] == "blueberry", Or(house_child[h+1] == "Fred",
                                                         house_child[h+2] == "Fred",
                                                         house_child[h+3] == "Fred",
                                                         house_child[h+4] == "Fred",
                                                         house_child[h+5] == "Fred")))

# Clue 3: Alice is not in the fifth house.
solver.add(house_name[5] != "Alice")

# Clue 4: The person's child is named Samantha is not in the second house.
solver.add(house_child[2] != "Samantha")

# Clue 5: The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies.
for h in range(1, 6):
    solver.add(Implies(house_smoothie[h] == "cherry", Or(house_smoothie[h+1] == "watermelon",
                                                        house_smoothie[h+2] == "watermelon",
                                                        house_smoothie[h+3] == "watermelon",
                                                        house_smoothie[h+4] == "watermelon",
                                                        house_smoothie[h+5] == "watermelon")))

# Clue 6: Alice is the person's child is named Alice.
solver.add(house_child[names.index("Alice") + 1] == "Alice")

# Clue 7: Alice is the Watermelon smoothie lover.
solver.add(house_smoothie[names.index("Alice") + 1] == "watermelon")

# Clue 8: Peter is somewhere to the right of the person's child is named Samantha.
for h in range(1, 6):
    solver.add(Implies(house_child[h] == "Samantha", Or(house_name[h+1] == "Peter",
                                                       house_name[h+2] == "Peter",
                                                       house_name[h+3] == "Peter",
                                                       house_name[h+4] == "Peter",
                                                       house_name[h+5] == "Peter")))

# Clue 9: Arnold is not in the second house.
solver.add(house_name[2] != "Arnold")

# Clue 10: Bob is the person who is the mother of Timothy.
solver.add(house_child[names.index("Bob") + 1] == "Timothy")

# Clue 11: Arnold is directly left of Carol.
for h in range(1, 6):
    solver.add(Implies(house_name[h] == "Arnold", house_name[h+1] == "Carol"))

# Clue 12: The person who likes Cherry smoothies is directly left of the person's child is named Samantha.
for h in range(1, 6):
    solver.add(Implies(house_smoothie[h] == "cherry", house_child[h+1] == "Samantha"))

# Clue 13: The person's child is named Meredith is in the sixth house.
solver.add(house_child[6] == "Meredith")

# Clue 14: The Dragonfruit smoothie lover is the person's child is named Meredith.
solver.add(house_smoothie[6] == "dragonfruit")

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    solution = []
    for h in houses:
        name = model[house_name[h]].as_string()[1:-1]
        child = model[house_child[h]].as_string()[1:-1]
        smoothie = model[house_smoothie[h]].as_string()[1:-1]
        solution.append([str(h), name, child, smoothie])
    
    # Print the solution in the required format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "Children", "Smoothie"],' +
          '"rows": ' + str(solution).replace("'", '"') +
          '}}')
else:
    print("No solution found")