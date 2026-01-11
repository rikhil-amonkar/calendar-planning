from z3 import *

# Define the variables for each house
names = [String('name_%d' % i) for i in range(5)]
smoothies = [String('smoothie_%d' % i) for i in range(5)]
nationalities = [String('nationality_%d' % i) for i in range(5)]

# Create a solver instance
solver = Solver()

# Define the domains for each variable
possible_names = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
possible_smoothies = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
possible_nationalities = ['german', 'swede', 'norwegian', 'dane', 'brit']

for var in names + smoothies + nationalities:
    solver.add(Or([var == n for n in possible_names + possible_smoothies + possible_nationalities]))

# Encode the clues as constraints
# Clue 1 and 2: The Dragonfruit smoothie lover is in the second house.
solver.add(smoothies[1] == 'dragonfruit')

# Clue 3: The Dragonfruit smoothie lover is somewhere to the left of Eric.
# This is already satisfied by clue 2 since Eric cannot be in the second house.

# Clue 4: Peter is not in the first house.
solver.add(names[0] != 'Peter')

# Clue 5: The Dane and the British person are next to each other.
next_to_each_other = Or(
    And(nationalities[0] == 'dane', nationalities[1] == 'brit'),
    And(nationalities[0] == 'brit', nationalities[1] == 'dane'),
    And(nationalities[1] == 'dane', nationalities[2] == 'brit'),
    And(nationalities[1] == 'brit', nationalities[2] == 'dane'),
    And(nationalities[2] == 'dane', nationalities[3] == 'brit'),
    And(nationalities[2] == 'brit', nationalities[3] == 'dane'),
    And(nationalities[3] == 'dane', nationalities[4] == 'brit'),
    And(nationalities[3] == 'brit', nationalities[4] == 'dane')
)
solver.add(next_to_each_other)

# Clue 6: The Desert smoothie lover is not in the fifth house.
solver.add(smoothies[4] != 'desert')

# Clue 7: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
# Since dragonfruit is in house 2, swede must be in house 1.
solver.add(nationalities[0] == 'swede')

# Clue 8: There are two houses between the person who drinks Lime smoothies and the Dane.
two_houses_between = Or(
    And(smoothies[0] == 'lime', nationalities[3] == 'dane'),
    And(smoothies[0] == 'lime', nationalities[4] == 'dane'),
    And(smoothies[1] == 'lime', nationalities[4] == 'dane'),
    And(smoothies[2] == 'lime', nationalities[0] == 'dane'),
    And(smoothies[2] == 'lime', nationalities[1] == 'dane'),
    And(smoothies[3] == 'lime', nationalities[0] == 'dane')
)
solver.add(two_houses_between)

# Clue 9: Bob is the Dane.
solver.add(nationalities[i] == 'dane' for i in range(5)).only_one()
solver.add(nationalities[nationalities.index('dane')] == 'bob')

# Clue 10: Alice is the Norwegian.
solver.add(nationalities[i] == 'norwegian' for i in range(5)).only_one()
solver.add(nationalities[nationalities.index('norwegian')] == 'alice')

# Clue 11: Alice is in the third house.
solver.add(names[2] == 'alice')

# Clue 12: The Watermelon smoothie lover is in the third house.
solver.add(smoothies[2] == 'watermelon')

# Ensure all names, smoothies, and nationalities are unique
solver.add(Distinct(names))
solver.add(Distinct(smoothies))
solver.add(Distinct(nationalities))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": []
        }
    }
    for i in range(5):
        house = str(i + 1)
        name = model[names[i]].as_string()[1:-1]
        smoothie = model[smoothies[i]].as_string()[1:-1]
        nationality = model[nationalities[i]].as_string()[1:-1]
        solution["solution"]["rows"].append([house, name, smoothie, nationality])
    print(solution)
else:
    print("No solution found")