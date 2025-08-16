from z3 import *

# Create variables for the names and occupations
names = ['Arnold', 'Eric', 'Peter', 'Alice']
occupations = ['doctor', 'engineer', 'artist', 'teacher']

# Create a solver instance
solver = Solver()

# Create dictionaries to map names and occupations to variables
name_vars = {name: Int(f'name_{name}') for name in names}
occupation_vars = {occupation: Int(f'occupation_{occupation}') for occupation in occupations}

# Define the domain for each variable (houses 1 to 4)
for var in list(name_vars.values()) + list(occupation_vars.values()):
    solver.add(var >= 1, var <= 4)

# Ensure all names and occupations are unique
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(occupation_vars.values())))

# Add the clues as constraints
# Clue 1: There are two houses between Eric and Peter.
solver.add(Abs(name_vars['Eric'] - name_vars['Peter']) == 3)

# Clue 2: The person who is a teacher is Peter.
solver.add(occupation_vars['teacher'] == name_vars['Peter'])

# Clue 3: Peter is not in the first house.
solver.add(name_vars['Peter'] != 1)

# Clue 4: There is one house between the person who is a doctor and Alice.
solver.add(Abs(name_vars['Alice'] - occupation_vars['doctor']) == 2)

# Clue 5: The person who is an artist is Alice.
solver.add(occupation_vars['artist'] == name_vars['Alice'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": []
        }
    }
    
    # Create a mapping from house number to name and occupation
    house_to_name = {model.evaluate(name_vars[name]).as_long(): name for name in names}
    house_to_occupation = {model.evaluate(occupation_vars[occupation]).as_long(): occupation for occupation in occupations}
    
    # Populate the solution rows
    for house in range(1, 5):
        name = house_to_name[house]
        occupation = house_to_occupation[house]
        solution["solution"]["rows"].append([str(house), name, occupation])
    
    # Print the solution as JSON
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")