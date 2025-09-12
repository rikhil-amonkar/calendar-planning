from z3 import *

# Define the domain for houses
houses = [1, 2, 3, 4, 5, 6]

# Define the variables for each characteristic
names = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
occupations = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
car_models = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']

# Create Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
occupation_vars = {house: Int(f'occupation_{house}') for house in houses}
car_model_vars = {house: Int(f'car_model_{house}') for house in houses}

# Create the solver
solver = Solver()

# Add constraints for unique assignments
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([occupation_vars[house] for house in houses]))
solver.add(Distinct([car_model_vars[house] for house in houses]))

# Map values to integers
name_map = {name: i for i, name in enumerate(names)}
occupation_map = {occupation: i for i, occupation in enumerate(occupations)}
car_model_map = {car_model: i for i, car_model in enumerate(car_models)}

# Add clues as constraints
# 1. The person who owns a Ford F-150 is in the fifth house.
solver.add(car_model_vars[5] == car_model_map['ford f150'])

# 2. The person who owns a Chevrolet Silverado is not in the second house.
solver.add(car_model_vars[2] != car_model_map['chevrolet silverado'])

# 3. The person who owns a Honda Civic and Peter are next to each other.
clue_3_constraints = [
    And(car_model_vars[house] == car_model_map['honda civic'], name_vars[house + 1] == name_map['Peter'])
    for house in range(1, 6)
] + [
    And(car_model_vars[house] == car_model_map['honda civic'], name_vars[house - 1] == name_map['Peter'])
    for house in range(2, 7)
]
solver.add(Or(clue_3_constraints))

# 4. The person who is a lawyer is not in the fifth house.
solver.add(occupation_vars[5] != occupation_map['lawyer'])

# 5. The person who is a nurse is directly left of the person who is an artist.
clue_5_constraints = [
    And(occupation_vars[house] == occupation_map['nurse'], occupation_vars[house + 1] == occupation_map['artist'])
    for house in range(1, 6)
]
solver.add(Or(clue_5_constraints))

# 6. Carol is somewhere to the right of Eric.
clue_6_constraints = [
    And(name_vars[house1] == name_map['Carol'], name_vars[house2] == name_map['Eric'])
    for house1 in range(2, 7) for house2 in range(1, house1)
]
solver.add(Or(clue_6_constraints))

# 7. The person who is a doctor is Eric.
clue_7_constraints = [
    And(name_vars[house] == name_map['Eric'], occupation_vars[house] == occupation_map['doctor'])
    for house in houses
]
solver.add(Or(clue_7_constraints))

# 8. The person who is a teacher is somewhere to the left of the person who is a nurse.
clue_8_constraints = [
    And(occupation_vars[house] == occupation_map['teacher'], occupation_vars[house + offset] == occupation_map['nurse'])
    for house in range(1, 6) for offset in range(1, 6-house+1)
]
solver.add(Or(clue_8_constraints))

# 9. Carol is not in the sixth house.
solver.add(name_vars[6] != name_map['Carol'])

# 10. The person who is an engineer is Bob.
clue_10_constraints = [
    And(name_vars[house] == name_map['Bob'], occupation_vars[house] == occupation_map['engineer'])
    for house in houses
]
solver.add(Or(clue_10_constraints))

# 11. The person who owns a Toyota Camry is the person who is a nurse.
clue_11_constraints = [
    And(car_model_vars[house] == car_model_map['toyota camry'], occupation_vars[house] == occupation_map['nurse'])
    for house in houses
]
solver.add(Or(clue_11_constraints))

# 12. There is one house between Peter and the person who is a lawyer.
clue_12_constraints = [
    And(name_vars[house] == name_map['Peter'], occupation_vars[house + 2] == occupation_map['lawyer'])
    for house in range(1, 5)
] + [
    And(name_vars[house] == name_map['Peter'], occupation_vars[house - 2] == occupation_map['lawyer'])
    for house in range(3, 7)
]
solver.add(Or(clue_12_constraints))

# 13. There is one house between the person who owns a Tesla Model 3 and Bob.
clue_13_constraints = [
    And(car_model_vars[house] == car_model_map['tesla model 3'], name_vars[house + 2] == name_map['Bob'])
    for house in range(1, 5)
] + [
    And(car_model_vars[house] == car_model_map['tesla model 3'], name_vars[house - 2] == name_map['Bob'])
    for house in range(3, 7)
]
solver.add(Or(clue_13_constraints))

# 14. Arnold is the person who is an artist.
clue_14_constraints = [
    And(name_vars[house] == name_map['Arnold'], occupation_vars[house] == occupation_map['artist'])
    for house in houses
]
solver.add(Or(clue_14_constraints))

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation", "CarModel"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        occupation = occupations[model[occupation_vars[house]].as_long()]
        car_model = car_models[model[car_model_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, occupation, car_model])
    import json
    print(json.dumps(solution))
else:
    print("No solution found")