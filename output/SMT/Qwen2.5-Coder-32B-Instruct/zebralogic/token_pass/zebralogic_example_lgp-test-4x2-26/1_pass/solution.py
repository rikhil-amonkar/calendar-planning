from z3 import *

# Define the solver
solver = Solver()

# Define the variables for names and occupations
names = [Int(f'name_{i}') for i in range(1, 5)]
occupations = [Int(f'occupation_{i}') for i in range(1, 5)]

# Define the constants for names and occupations
name_map = {'Arnold': 0, 'Eric': 1, 'Peter': 2, 'Alice': 3}
occupation_map = {'doctor': 0, 'engineer': 1, 'artist': 2, 'teacher': 3}

# Add constraints for unique names and occupations
solver.add(Distinct(names))
solver.add(Distinct(occupations))

# Add constraints based on the clues
# Clue 1: There are two houses between Eric and Peter.
# Clue 3: Peter is not in the first house, so Peter must be in house 4.
solver.add(names[3] == name_map['Peter'])  # Peter is in house 4

# Clue 2: The person who is a teacher is Peter.
solver.add(occupations[3] == occupation_map['teacher'])

# Clue 4: There is one house between the person who is a doctor and Alice.
# Clue 5: The person who is an artist is Alice.
# This means Alice can be in house 2 or house 3, and the doctor must be in the adjacent house.
alice_house = Or(names[1] == name_map['Alice'], names[2] == name_map['Alice'])
doctor_adjacent = Or(
    And(names[1] == name_map['Alice'], occupations[0] == occupation_map['doctor']),
    And(names[1] == name_map['Alice'], occupations[2] == occupation_map['doctor']),
    And(names[2] == name_map['Alice'], occupations[1] == occupation_map['doctor']),
    And(names[2] == name_map['Alice'], occupations[3] == occupation_map['doctor'])
)

solver.add(alice_house)
solver.add(doctor_adjacent)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": []
        }
    }
    
    for i in range(4):
        house = str(i + 1)
        name = [k for k, v in name_map.items() if v == model[names[i]].as_long()][0]
        occupation = [k for k, v in occupation_map.items() if v == model[occupations[i]].as_long()][0]
        solution["solution"]["rows"].append([house, name, occupation])
    
    print(solution)
else:
    print("No solution found")