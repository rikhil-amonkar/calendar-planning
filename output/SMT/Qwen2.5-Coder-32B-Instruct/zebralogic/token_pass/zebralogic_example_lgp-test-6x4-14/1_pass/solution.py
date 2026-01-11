from z3 import *

# Define symbolic variables
houses = range(6)
names = [String(f'name_{i}') for i in houses]
car_models = [String(f'car_model_{i}') for i in houses]
mothers = [String(f'mother_{i}') for i in houses]
hobbies = [String(f'hobby_{i}') for i in houses]

# Define domains
people = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
car_models_list = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
mothers_list = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
hobbies_list = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']

# Create solver
solver = Solver()

# Add constraints for unique assignments
solver.add(Distinct(names))
solver.add(Distinct(car_models))
solver.add(Distinct(mothers))
solver.add(Distinct(hobbies))

# Add domain constraints
for var in names + car_models + mothers + hobbies:
    solver.add(Or([var == val for val in people + car_models_list + mothers_list + hobbies_list]))

# Clues
# 1. The person who owns a Toyota Camry is in the sixth house.
solver.add(car_models[5] == 'toyota camry')

# 2. Carol is the photography enthusiast.
solver.add(Or([And(names[i] == 'Carol', hobbies[i] == 'photography') for i in houses]))

# 3. The person who owns a Chevrolet Silverado is The person whose mother's name is Aniya.
solver.add(Or([And(car_models[i] == 'chevrolet silverado', mothers[i] == 'Aniya') for i in houses]))

# 4. The person who owns a Chevrolet Silverado is not in the second house.
solver.add(car_models[1] != 'chevrolet silverado')

# 5. The person who owns a Ford F-150 is The person whose mother's name is Sarah.
solver.add(Or([And(car_models[i] == 'ford f150', mothers[i] == 'Sarah') for i in houses]))

# 6. The person who owns a BMW 3 Series is Bob.
solver.add(Or([And(car_models[i] == 'bmw 3 series', names[i] == 'Bob') for i in houses]))

# 7. The person whose mother's name is Kailyn is in the sixth house.
solver.add(mothers[5] == 'Kailyn')

# 8. Eric is directly left of the person who enjoys knitting.
solver.add(Or([And(names[i] == 'Eric', hobbies[i+1] == 'knitting') for i in range(5)]))

# 9. There is one house between The person whose mother's name is Sarah and the person who owns a Toyota Camry.
solver.add(Or([Abs(i - j) == 2 for i in range(6) for j in range(6) if i != j]) & Or([And(mothers[i] == 'Sarah', car_models[j] == 'toyota camry') for i in range(6) for j in range(6) if i != j]))

# 10. The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
solver.add(Or([And(mothers[i] == 'Penny', hobbies[j] == 'knitting') for i in range(1, 6) for j in range(i)]))

# 11. The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
solver.add(Or([And(mothers[i] == 'Aniya', car_models[j] == 'honda civic') for i in range(1, 6) for j in range(i)]))

# 12. Alice is somewhere to the right of the person who owns a Ford F-150.
solver.add(Or([And(names[i] == 'Alice', car_models[j] == 'ford f150') for i in range(1, 6) for j in range(i)]))

# 13. Eric is the person who enjoys gardening.
solver.add(Or([And(names[i] == 'Eric', hobbies[i] == 'gardening') for i in houses]))

# 14. The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
solver.add(Or([And(hobbies[i] == 'woodworking', hobbies[j] == 'knitting') for i in range(5) for j in range(i+1, 6)]))

# 15. There is one house between The person whose mother's name is Sarah and the person who loves cooking.
solver.add(Or([Abs(i - j) == 2 for i in range(6) for j in range(6) if i != j]) & Or([And(mothers[i] == 'Sarah', hobbies[j] == 'cooking') for i in range(6) for j in range(6) if i != j]))

# 16. The person who owns a Honda Civic is Arnold.
solver.add(Or([And(car_models[i] == 'honda civic', names[i] == 'Arnold') for i in houses]))

# 17. The person whose mother's name is Holly is directly left of the person who enjoys knitting.
solver.add(Or([And(mothers[i] == 'Holly', hobbies[i+1] == 'knitting') for i in range(5)]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in houses:
        name = model[names[i]].as_string()[1:-1]
        car_model = model[car_models[i]].as_string()[1:-1]
        mother = model[mothers[i]].as_string()[1:-1]
        hobby = model[hobbies[i]].as_string()[1:-1]
        solution.append([str(i+1), name, car_model, mother, hobby])
    
    print('{"solution": {"header": ["House", "Name", "CarModel", "Mother", "Hobby"], "rows": %s}}' % solution)
else:
    print("No solution found")