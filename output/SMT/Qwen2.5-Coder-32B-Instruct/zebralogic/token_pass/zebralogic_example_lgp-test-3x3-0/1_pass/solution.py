from z3 import *

# Define the sets of possible values
names = ['Peter', 'Eric', 'Arnold']
educations = ['bachelor', 'associate', 'high school']
occupations = ['teacher', 'doctor', 'engineer']

# Create variables for each house
house_vars = {}
for house in range(1, 4):
    house_vars[house] = {
        'name': Int(f'name_{house}'),
        'education': Int(f'education_{house}'),
        'occupation': Int(f'occupation_{house}')
    }

# Create a solver instance
solver = Solver()

# Add constraints for each variable to be within the valid ranges
for house in range(1, 4):
    solver.add(house_vars[house]['name'] >= 0)
    solver.add(house_vars[house]['name'] <= 2)
    solver.add(house_vars[house]['education'] >= 0)
    solver.add(house_vars[house]['education'] <= 2)
    solver.add(house_vars[house]['occupation'] >= 0)
    solver.add(house_vars[house]['occupation'] <= 2)

# Ensure all names, educations, and occupations are unique
solver.add(Distinct([house_vars[house]['name'] for house in range(1, 4)]))
solver.add(Distinct([house_vars[house]['education'] for house in range(1, 4)]))
solver.add(Distinct([house_vars[house]['occupation'] for house in range(1, 4)]))

# Translate clues into constraints
# Clue 1: The person who is a teacher is directly left of the person with an associate's degree.
solver.add(Or(
    And(house_vars[1]['occupation'] == occupations.index('teacher'), house_vars[2]['education'] == educations.index('associate')),
    And(house_vars[2]['occupation'] == occupations.index('teacher'), house_vars[3]['education'] == educations.index('associate'))
))

# Clue 2: The person with an associate's degree and Eric are next to each other.
solver.add(Or(
    And(house_vars[1]['education'] == educations.index('associate'), house_vars[2]['name'] == names.index('Eric')),
    And(house_vars[2]['education'] == educations.index('associate'), house_vars[1]['name'] == names.index('Eric')),
    And(house_vars[2]['education'] == educations.index('associate'), house_vars[3]['name'] == names.index('Eric')),
    And(house_vars[3]['education'] == educations.index('associate'), house_vars[2]['name'] == names.index('Eric'))
))

# Clue 3: Peter is the person with a high school diploma.
solver.add(house_vars[1]['name'] == names.index('Peter') ==>
           house_vars[1]['education'] == educations.index('high school'))
solver.add(house_vars[2]['name'] == names.index('Peter') ==>
           house_vars[2]['education'] == educations.index('high school'))
solver.add(house_vars[3]['name'] == names.index('Peter') ==>
           house_vars[3]['education'] == educations.index('high school'))

# Clue 4: The person who is a doctor is the person with a bachelor's degree.
solver.add(Or(
    And(house_vars[1]['occupation'] == occupations.index('doctor'), house_vars[1]['education'] == educations.index('bachelor')),
    And(house_vars[2]['occupation'] == occupations.index('doctor'), house_vars[2]['education'] == educations.index('bachelor')),
    And(house_vars[3]['occupation'] == occupations.index('doctor'), house_vars[3]['education'] == educations.index('bachelor'))
))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Occupation"],
            "rows": []
        }
    }
    for house in range(1, 4):
        name = names[model.eval(house_vars[house]['name']).as_long()]
        education = educations[model.eval(house_vars[house]['education']).as_long()]
        occupation = occupations[model.eval(house_vars[house]['occupation']).as_long()]
        solution["solution"]["rows"].append([str(house), name, education, occupation])
    
    print(solution)
else:
    print("No solution found")