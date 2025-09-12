from z3 import *
import json

# Define the variables
names = ['Arnold', 'Eric']
educations = ['associate', 'high school']
heights = ['short', 'very short']
foods = ['grilled cheese', 'pizza']
drinks = ['tea', 'water']
houses = [1, 2]

# Create the solver
solver = Solver()

# Define the arrays for each attribute
name = [String(f'name_{i}') for i in houses]
education = [String(f'education_{i}') for i in houses]
height = [String(f'height_{i}') for i in houses]
food = [String(f'food_{i}') for i in houses]
drink = [String(f'drink_{i}') for i in houses]

# Add domain constraints
for h in houses:
    solver.add(name[h-1] == Or(*[s for s in names]))
    solver.add(education[h-1] == Or(*[s for s in educations]))
    solver.add(height[h-1] == Or(*[s for s in heights]))
    solver.add(food[h-1] == Or(*[s for s in foods]))
    solver.add(drink[h-1] == Or(*[s for s in drinks]))

# Add uniqueness constraints
solver.add(Distinct(name))
solver.add(Distinct(education))
solver.add(Distinct(height))
solver.add(Distinct(food))
solver.add(Distinct(drink))

# Add clue constraints
# 1. The person who is very short is the person who is a pizza lover.
solver.add(Implies(height[0] == 'very short', food[0] == 'pizza'))
solver.add(Implies(height[1] == 'very short', food[1] == 'pizza'))

# 2. The person who loves eating grilled cheese is in the second house.
solver.add(food[1] == 'grilled cheese')

# 3. The person with a high school diploma is the person who is a pizza lover.
solver.add(Implies(education[0] == 'high school', food[0] == 'pizza'))
solver.add(Implies(education[1] == 'high school', food[1] == 'pizza'))

# 4. The tea drinker is the person who loves eating grilled cheese.
solver.add(Implies(drink[0] == 'tea', food[0] == 'grilled cheese'))
solver.add(Implies(drink[1] == 'tea', food[1] == 'grilled cheese'))

# 5. Arnold is the person who is a pizza lover.
solver.add(Or(And(name[0] == 'Arnold', food[0] == 'pizza'), And(name[1] == 'Arnold', food[1] == 'pizza')))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
            "rows": [
                [str(h), str(model[name[h-1]]), str(model[education[h-1]]), str(model[height[h-1]]), str(model[food[h-1]]), str(model[drink[h-1]])]
                for h in houses
            ]
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")