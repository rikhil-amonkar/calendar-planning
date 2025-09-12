from z3 import *

# Create a solver instance
solver = Solver()

# Define the variables
houses = [1, 2, 3]
names = ['Peter', 'Arnold', 'Eric']
occupations = ['doctor', 'teacher', 'engineer']
hobbies = ['cooking', 'photography', 'gardening']

# Create dictionaries to hold the Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
occupation_vars = {house: Int(f'occupation_{house}') for house in houses}
hobby_vars = {house: Int(f'hobby_{house}') for house in houses}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([occupation_vars[house] for house in houses]))
solver.add(Distinct([hobby_vars[house] for house in houses]))

# Map names, occupations, and hobbies to integers
name_map = {name: i for i, name in enumerate(names)}
occupation_map = {occupation: i for i, occupation in enumerate(occupations)}
hobby_map = {hobby: i for i, hobby in enumerate(hobbies)}

# Add constraints based on the clues
# Clue 1: The person who is a doctor and Eric are next to each other.
for house in houses[:-1]:
    solver.add(Or(
        And(occupation_vars[house] == occupation_map['doctor'], name_vars[house + 1] == name_map['Eric']),
        And(name_vars[house] == name_map['Eric'], occupation_vars[house + 1] == occupation_map['doctor'])
    ))

# Clue 2: The person who loves cooking is directly left of the person who is a teacher.
for house in houses[:-1]:
    solver.add(And(hobby_vars[house] == hobby_map['cooking'], occupation_vars[house + 1] == occupation_map['teacher']))

# Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
solver.add(Or(
    And(hobby_vars[1] == hobby_map['gardening'], occupation_vars[2] == occupation_map['doctor']),
    And(hobby_vars[1] == hobby_map['gardening'], occupation_vars[3] == occupation_map['doctor']),
    And(hobby_vars[2] == hobby_map['gardening'], occupation_vars[3] == occupation_map['doctor'])
))

# Clue 4: The photography enthusiast is the person who is a teacher.
for house in houses:
    solver.add(Implies(hobby_vars[house] == hobby_map['photography'], occupation_vars[house] == occupation_map['teacher']))

# Clue 5: The person who is an engineer is Peter.
for house in houses:
    solver.add(Implies(occupation_vars[house] == occupation_map['engineer'], name_vars[house] == name_map['Peter']))

# Ensure that all values are within the correct range
for house in houses:
    solver.add(And(name_vars[house] >= 0, name_vars[house] < len(names)))
    solver.add(And(occupation_vars[house] >= 0, occupation_vars[house] < len(occupations)))
    solver.add(And(hobby_vars[house] >= 0, hobby_vars[house] < len(hobbies)))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        occupation = occupations[model.evaluate(occupation_vars[house]).as_long()]
        hobby = hobbies[model.evaluate(hobby_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, occupation, hobby])
    import json
    print(json.dumps(solution))
else:
    print("No solution found")