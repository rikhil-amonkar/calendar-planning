from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
names = ['Arnold', 'Eric', 'Peter', 'Alice']
occupations = ['doctor', 'engineer', 'artist', 'teacher']
houses = [1, 2, 3, 4]

# Create integer variables for each person's house number
house_of = {name: Int(f'house_of_{name}') for name in names}
occupation_of = {name: String(f'occupation_of_{name}') for name in names}

# Add constraints for unique house numbers
solver.add(Distinct([house_of[name] for name in names]))
for name in names:
    solver.add(And(house_of[name] >= 1, house_of[name] <= 4))

# Add constraints for unique occupations
solver.add(Distinct([occupation_of[name] for name in names]))

# Clue 1: There are two houses between Eric and Peter.
solver.add(Abs(house_of['Eric'] - house_of['Peter']) == 3)

# Clue 2: The person who is a teacher is Peter.
solver.add(occupation_of['Peter'] == 'teacher')

# Clue 3: Peter is not in the first house.
solver.add(house_of['Peter'] != 1)

# Clue 4: There is one house between the person who is a doctor and Alice.
solver.add(Abs(house_of['Alice'] - house_of[name]) == 2 for name in names if occupation_of[name] == 'doctor')

# Clue 5: The person who is an artist is Alice.
solver.add(occupation_of['Alice'] == 'artist')

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": []
        }
    }
    
    # Extract the solution
    for house in houses:
        for name in names:
            if model.evaluate(house_of[name]) == house:
                occupation = model.evaluate(occupation_of[name]).as_string()[1:-1]  # Remove quotes
                solution["solution"]["rows"].append([str(house), name, occupation])
    
    # Print the solution as JSON
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")