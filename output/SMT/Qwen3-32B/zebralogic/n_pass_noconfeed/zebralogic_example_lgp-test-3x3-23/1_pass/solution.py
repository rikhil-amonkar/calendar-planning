from z3 import *
import json

# Define constants for easier handling
name_peter = 0
name_arnold = 1
name_eric = 2

occupation_doctor = 0
occupation_teacher = 1
occupation_engineer = 2

hobby_cooking = 0
hobby_photography = 1
hobby_gardening = 2

# Create solver
s = Solver()

# Create variables for each house (0-based index)
names = [Int('name_%d' % i) for i in range(3)]
occupations = [Int('occupation_%d' % i) for i in range(3)]
hobbies = [Int('hobby_%d' % i) for i in range(3)]

# Add constraints for permutations
for var in [names, occupations, hobbies]:
    s.add([And(0 <= v, v <= 2) for v in var])
    s.add(Distinct(var))

# Clue 5: The person who is an engineer is Peter.
for i in range(3):
    s.add(Implies(occupations[i] == occupation_engineer, names[i] == name_peter))

# Clue 4: The photography enthusiast is the person who is a teacher.
for i in range(3):
    s.add(Implies(occupations[i] == occupation_teacher, hobbies[i] == hobby_photography))

# Clue 2: The person who loves cooking is directly left of the person who is a teacher.
s.add(Or(
    And(hobbies[0] == hobby_cooking, occupations[1] == occupation_teacher),
    And(hobbies[1] == hobby_cooking, occupations[2] == occupation_teacher)
))

# Clue 1: The person who is a doctor and Eric are next to each other.
s.add(Or(
    And(occupations[0] == occupation_doctor, names[1] == name_eric),
    And(occupations[1] == occupation_doctor, names[0] == name_eric),
    And(occupations[1] == occupation_doctor, names[2] == name_eric),
    And(occupations[2] == occupation_doctor, names[1] == name_eric)
))

# Clue 3: The doctor is to the right of the gardening person.
doctor_pos = Int('doctor_pos')
gardening_pos = Int('gardening_pos')

s.add(Or(
    And(occupations[0] == occupation_doctor, doctor_pos == 0),
    And(occupations[1] == occupation_doctor, doctor_pos == 1),
    And(occupations[2] == occupation_doctor, doctor_pos == 2)
))
s.add(Or(
    And(hobbies[0] == hobby_gardening, gardening_pos == 0),
    And(hobbies[1] == hobby_gardening, gardening_pos == 1),
    And(hobbies[2] == hobby_gardening, gardening_pos == 2)
))
s.add(And(0 <= doctor_pos, doctor_pos <= 2))
s.add(And(0 <= gardening_pos, gardening_pos <= 2))
s.add(doctor_pos > gardening_pos)

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    
    # Create mappings from integer values to strings
    name_map = {0: 'Peter', 1: 'Arnold', 2: 'Eric'}
    occupation_map = {0: 'doctor', 1: 'teacher', 2: 'engineer'}
    hobby_map = {0: 'cooking', 1: 'photography', 2: 'gardening'}
    
    # Extract the solution
    solution_rows = []
    for i in range(3):
        house_num = i + 1
        name_val = model[names[i]].as_long()
        occ_val = model[occupations[i]].as_long()
        hobby_val = model[hobbies[i]].as_long()
        solution_rows.append([
            str(house_num),
            name_map[name_val],
            occupation_map[occ_val],
            hobby_map[hobby_val]
        ])
    
    # Format as JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Hobby"],
            "rows": solution_rows
        }
    }
    
    # Print JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")