from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = range(1, 7)
names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
car_models = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']

# Declare variables for each attribute
name_vars = {house: Int(f'name_{house}') for house in houses}
car_model_vars = {house: Int(f'car_model_{house}') for house in houses}
mother_vars = {house: Int(f'mother_{house}') for house in houses}
hobby_vars = {house: Int(f'hobby_{house}') for house in houses}

# Map indices to values
name_map = {name: i for i, name in enumerate(names)}
car_model_map = {car_model: i for i, car_model in enumerate(car_models)}
mother_map = {mother: i for i, mother in enumerate(mothers)}
hobby_map = {hobby: i for i, hobby in enumerate(hobbies)}

# Add constraints for unique values in each category
for var_dict in [name_vars, car_model_vars, mother_vars, hobby_vars]:
    solver.add(Distinct(var_dict.values()))

# Clue 1: The person who owns a Toyota Camry is in the sixth house.
solver.add(car_model_vars[6] == car_model_map['toyota camry'])

# Clue 2: Carol is the photography enthusiast.
solver.add(name_vars[i] == name_map['Carol'] for i in houses if hobby_vars[i] == hobby_map['photography'])

# Clue 3: The person who owns a Chevrolet Silverado is The person whose mother's name is Aniya.
solver.add(And(car_model_vars[i] == car_model_map['chevrolet silverado'], mother_vars[i] == mother_map['Aniya']) for i in houses)

# Clue 4: The person who owns a Chevrolet Silverado is not in the second house.
solver.add(car_model_vars[2] != car_model_map['chevrolet silverado'])

# Clue 5: The person who owns a Ford F-150 is The person whose mother's name is Sarah.
solver.add(And(car_model_vars[i] == car_model_map['ford f150'], mother_vars[i] == mother_map['Sarah']) for i in houses)

# Clue 6: The person who owns a BMW 3 Series is Bob.
solver.add(And(car_model_vars[i] == car_model_map['bmw 3 series'], name_vars[i] == name_map['Bob']) for i in houses)

# Clue 7: The person whose mother's name is Kailyn is in the sixth house.
solver.add(mother_vars[6] == mother_map['Kailyn'])

# Clue 8: Eric is directly left of the person who enjoys knitting.
solver.add(Or([And(name_vars[i] == name_map['Eric'], hobby_vars[i+1] == hobby_map['knitting']) for i in range(1, 6)]))

# Clue 9: There is one house between The person whose mother's name is Sarah and the person who owns a Toyota Camry.
solver.add(Or([And(mother_vars[i] == mother_map['Sarah'], car_model_vars[i+2] == car_model_map['toyota camry']) for i in range(1, 5)] +
              [And(mother_vars[i] == mother_map['Sarah'], car_model_vars[i-2] == car_model_map['toyota camry']) for i in range(3, 7)]))

# Clue 10: The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
solver.add(Or([And(mother_vars[j] == mother_map['Penny'], hobby_vars[i] == hobby_map['knitting']) for i in range(1, 6) for j in range(i+1, 7)]))

# Clue 11: The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
solver.add(Or([And(mother_vars[j] == mother_map['Aniya'], car_model_vars[i] == car_model_map['honda civic']) for i in range(1, 6) for j in range(i+1, 7)]))

# Clue 12: Alice is somewhere to the right of the person who owns a Ford F-150.
solver.add(Or([And(name_vars[j] == name_map['Alice'], car_model_vars[i] == car_model_map['ford f150']) for i in range(1, 6) for j in range(i+1, 7)]))

# Clue 13: Eric is the person who enjoys gardening.
solver.add(And(name_vars[i] == name_map['Eric'], hobby_vars[i] == hobby_map['gardening']) for i in houses)

# Clue 14: The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
solver.add(Or([And(hobby_vars[i] == hobby_map['woodworking'], hobby_vars[j] == hobby_map['knitting']) for i in range(1, 6) for j in range(i+1, 7)]))

# Clue 15: There is one house between The person whose mother's name is Sarah and the person who loves cooking.
solver.add(Or([And(mother_vars[i] == mother_map['Sarah'], hobby_vars[i+2] == hobby_map['cooking']) for i in range(1, 5)] +
              [And(mother_vars[i] == mother_map['Sarah'], hobby_vars[i-2] == hobby_map['cooking']) for i in range(3, 7)]))

# Clue 16: The person who owns a Honda Civic is Arnold.
solver.add(And(car_model_vars[i] == car_model_map['honda civic'], name_vars[i] == name_map['Arnold']) for i in houses)

# Clue 17: The person whose mother's name is Holly is directly left of the person who enjoys knitting.
solver.add(Or([And(mother_vars[i] == mother_map['Holly'], hobby_vars[i+1] == hobby_map['knitting']) for i in range(1, 6)]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        car_model = car_models[model[car_model_vars[house]].as_long()]
        mother = mothers[model[mother_vars[house]].as_long()]
        hobby = hobbies[model[hobby_vars[house]].as_long()]
        solution.append([str(house), name, car_model, mother, hobby])
    
    print('{' + f'"solution": {{"header": ["House", "Name", "CarModel", "Mother", "Hobby"], "rows": {solution}}}' + '}')
else:
    print("No solution found")