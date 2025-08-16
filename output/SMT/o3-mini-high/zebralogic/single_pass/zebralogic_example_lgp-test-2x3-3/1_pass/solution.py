from z3 import Solver, Int, Distinct, Or, If
import json

# Create a solver instance
s = Solver()

# We have 2 houses: index 0 for House 1, index 1 for House 2.
num_houses = 2

# For each house, we create three integer variables: name, food, mother.
# We use the following mapping:
# Names: Arnold = 0, Eric = 1
# Food: grilled cheese = 0, pizza = 1
# Mothers: Holly = 0, Aniya = 1

names = [Int(f"name_{i}") for i in range(num_houses)]
foods = [Int(f"food_{i}") for i in range(num_houses)]
mothers = [Int(f"mother_{i}") for i in range(num_houses)]

# Each variable must be either 0 or 1.
for i in range(num_houses):
    s.add(Or(names[i] == 0, names[i] == 1))
    s.add(Or(foods[i] == 0, foods[i] == 1))
    s.add(Or(mothers[i] == 0, mothers[i] == 1))

# They are all distinct across houses for their category.
s.add(Distinct(names))
s.add(Distinct(foods))
s.add(Distinct(mothers))

# Clue 1: The person who loves eating grilled cheese is directly left of the person who is a pizza lover.
# With only 2 houses, the left house (house index 0) must have grilled cheese (0)
# and the right house (house index 1) must have pizza (1).
s.add(foods[0] == 0)
s.add(foods[1] == 1)

# Clue 2: Arnold is not in the second house.
# So house index 1 cannot be Arnold (Arnold is represented by 0).
s.add(names[1] != 0)

# Clue 3: Arnold is the person whose mother's name is Holly.
# For every house, if the resident is Arnold then the mother's must be Holly (0).
for i in range(num_houses):
    s.add(If(names[i] == 0, mothers[i] == 0, True))

# Since Arnold can't be in house 2, he must be in house 1 which is index 0.
s.add(names[0] == 0)

# Try to solve the constraints.
if s.check() == "sat" or s.check():
    m = s.model()
    
    # Mapping back from our integer codes to the actual values.
    name_mapping = {0: "Arnold", 1: "Eric"}
    food_mapping = {0: "grilled cheese", 1: "pizza"}
    mother_mapping = {0: "Holly", 1: "Aniya"}
    
    # Prepare the final solution dictionary.
    solution = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": [
                ["1", 
                 name_mapping[m.evaluate(names[0]).as_long()], 
                 food_mapping[m.evaluate(foods[0]).as_long()], 
                 mother_mapping[m.evaluate(mothers[0]).as_long()]
                ],
                ["2", 
                 name_mapping[m.evaluate(names[1]).as_long()], 
                 food_mapping[m.evaluate(foods[1]).as_long()], 
                 mother_mapping[m.evaluate(mothers[1]).as_long()]
                ]
            ]
        }
    }
    
    # Print the solution as JSON.
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")