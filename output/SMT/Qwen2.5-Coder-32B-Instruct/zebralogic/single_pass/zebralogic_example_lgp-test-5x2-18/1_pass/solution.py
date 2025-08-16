from z3 import *

# Define the variables
names = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
children = ['Timothy', 'Meredith', 'Samantha', 'Fred', 'Bella']
houses = range(1, 6)

# Create the solver
solver = Solver()

# Create the variables for the solver
name_vars = {house: Int(f'name_{house}') for house in houses}
child_vars = {house: Int(f'child_{house}') for house in houses}

# Add constraints for unique names and children
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(child_vars.values()))

# Map names and children to integers
name_map = {name: i for i, name in enumerate(names)}
child_map = {child: i for i, child in enumerate(children)}

# Constraint 1: Bob is somewhere to the left of the person's child is named Samantha.
bob_house = Int('bob_house')
samantha_house = Int('samantha_house')
solver.add(Or([And(name_vars[house] == name_map['Bob'], bob_house == house) for house in houses]))
solver.add(Or([And(child_vars[house] == child_map['Samantha'], samantha_house == house) for house in houses]))
solver.add(bob_house < samantha_house)

# Constraint 2: The person who is the mother of Timothy is somewhere to the left of the person's child is named Samantha.
timothy_house = Int('timothy_house')
solver.add(Or([And(child_vars[house] == child_map['Timothy'], timothy_house == house) for house in houses]))
solver.add(timothy_house < samantha_house)

# Constraint 3: The person's child is named Fred is in the second house.
solver.add(child_vars[2] == child_map['Fred'])

# Constraint 4: There is one house between Alice and the person's child is named Samantha.
alice_house = Int('alice_house')
solver.add(Or([And(name_vars[house] == name_map['Alice'], alice_house == house) for house in houses]))
solver.add(Or(alice_house == samantha_house - 2, alice_house == samantha_house + 2))

# Constraint 5: Eric is not in the third house.
solver.add(name_vars[3] != name_map['Eric'])

# Constraint 6: Bob is not in the third house.
solver.add(name_vars[3] != name_map['Bob'])

# Constraint 7: The person's child is named Fred is directly left of the person's child is named Bella.
bella_house = Int('bella_house')
solver.add(Or([And(child_vars[house] == child_map['Bella'], bella_house == house) for house in houses]))
solver.add(child_vars[2] == child_map['Fred'])
solver.add(child_vars[3] == child_map['Bella'])

# Constraint 8: The person's child is named Samantha is somewhere to the left of Peter.
peter_house = Int('peter_house')
solver.add(Or([And(name_vars[house] == name_map['Peter'], peter_house == house) for house in houses]))
solver.add(samantha_house < peter_house)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name_index = model[name_vars[house]].as_long()
        child_index = model[child_vars[house]].as_long()
        name = names[name_index]
        child = children[child_index]
        solution.append([str(house), name, child])
    
    # Print the solution in the required format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "Children"],' +
          f'"rows": {solution}' +
          '}}')
else:
    print("No solution found")