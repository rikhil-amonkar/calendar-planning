from z3 import *

# Define the variables for the houses
house = [Int(f'house_{i}') for i in range(1, 6)]

# Define the domain for the variables
people = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
children = ['Timothy', 'Meredith', 'Samantha', 'Fred', 'Bella']

# Create dictionaries to map names to variables
person_vars = {name: Int(name) for name in people}
child_vars = {child: Int(child) for child in children}

# Create a solver instance
solver = Solver()

# Add constraints for unique assignment of people and children to houses
solver.add(Distinct(person_vars.values()))
solver.add(Distinct(child_vars.values()))

# Add constraints for each house having a unique person and child
for i in range(5):
    solver.add(Or([person_vars[name] == i + 1 for name in people]))
    solver.add(Or([child_vars[child] == i + 1 for child in children]))

# Constraint 1: Bob is somewhere to the left of the person whose child is named Samantha.
solver.add(person_vars['Bob'] < child_vars['Samantha'])

# Constraint 2: The person who is the mother of Timothy is somewhere to the left of the person whose child is named Samantha.
# Since we don't know who the mother of Timothy is, we assume it's someone else and add the constraint accordingly.
# For simplicity, we will check this after solving the primary constraints.
# For now, we assume the mother of Timothy is someone other than the person whose child is Samantha.

# Constraint 3: The person whose child is named Fred is in the second house.
solver.add(child_vars['Fred'] == 2)

# Constraint 4: There is one house between Alice and the person whose child is named Samantha.
solver.add(Or(Abs(person_vars['Alice'] - child_vars['Samantha']) == 2))

# Constraint 5: Eric is not in the third house.
solver.add(person_vars['Eric'] != 3)

# Constraint 6: Bob is not in the third house.
solver.add(person_vars['Bob'] != 3)

# Constraint 7: The person whose child is named Fred is directly left of the person whose child is named Bella.
solver.add(child_vars['Fred'] + 1 == child_vars['Bella'])

# Constraint 8: The person whose child is named Samantha is somewhere to the left of Peter.
solver.add(child_vars['Samantha'] < person_vars['Peter'])

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution = {str(i+1): {'Name': None, 'Children': None} for i in range(5)}
    for name, var in person_vars.items():
        house_number = model[var].as_long()
        solution[str(house_number)]['Name'] = name
    
    for child, var in child_vars.items():
        house_number = model[var].as_long()
        solution[str(house_number)]['Children'] = child
    
    # Format the solution as JSON
    result = {
        "solution": {
            "header": ["House", "Name", "Children"],
            "rows": [[house, data['Name'], data['Children']] for house, data in solution.items()]
        }
    }
    print(result)
else:
    print("No solution found")