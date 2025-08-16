from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3, 4]
names = ['Eric', 'Peter', 'Alice', 'Arnold']
car_models = ['tesla model 3', 'honda civic', 'toyota camry', 'ford f150']
birthdays = ['jan', 'april', 'sept', 'feb']
hobbies = ['painting', 'cooking', 'gardening', 'photography']

# Declare variables for each characteristic
name_vars = {house: Int(f'name_{house}') for house in houses}
car_model_vars = {house: Int(f'car_model_{house}') for house in houses}
birthday_vars = {house: Int(f'birthday_{house}') for house in houses}
hobby_vars = {house: Int(f'hobby_{house}') for house in houses}

# Add constraints for unique values in each category
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(car_model_vars.values()))
solver.add(Distinct(birthday_vars.values()))
solver.add(Distinct(hobby_vars.values()))

# Map values to integers
name_map = {name: i for i, name in enumerate(names)}
car_model_map = {car_model: i for i, car_model in enumerate(car_models)}
birthday_map = {birthday: i for i, birthday in enumerate(birthdays)}
hobby_map = {hobby: i for i, hobby in enumerate(hobbies)}

# Add constraints based on clues
# 1. The person whose birthday is in January is not in the second house.
solver.add(birthday_vars[2] != birthday_map['jan'])

# 2. The photography enthusiast is somewhere to the left of Eric.
solver.add(Or(hobby_vars[1] == hobby_map['photography'], hobby_vars[2] == hobby_map['photography'], hobby_vars[3] == hobby_map['photography']))
solver.add(ForAll([house], Implies(hobby_vars[house] == hobby_map['photography'], ForAll([house2], Implies(name_vars[house2] == name_map['Eric'], house < house2)))))

# 3. The photography enthusiast is somewhere to the left of Peter.
solver.add(ForAll([house], Implies(hobby_vars[house] == hobby_map['photography'], ForAll([house2], Implies(name_vars[house2] == name_map['Peter'], house < house2)))))

# 4. The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
solver.add(Or(And(car_model_vars[1] == car_model_map['honda civic'], car_model_vars[2] == car_model_map['tesla model 3']),
              And(car_model_vars[2] == car_model_map['honda civic'], car_model_vars[3] == car_model_map['tesla model 3']),
              And(car_model_vars[3] == car_model_map['honda civic'], car_model_vars[4] == car_model_map['tesla model 3'])))

# 5. There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
solver.add(Or(And(car_model_vars[1] == car_model_map['tesla model 3'], hobby_vars[3] == hobby_map['gardening']),
              And(car_model_vars[2] == car_model_map['tesla model 3'], hobby_vars[4] == hobby_map['gardening']),
              And(car_model_vars[3] == car_model_map['tesla model 3'], hobby_vars[1] == hobby_map['gardening']),
              And(car_model_vars[4] == car_model_map['tesla model 3'], hobby_vars[2] == hobby_map['gardening'])))

# 6. The person who owns a Tesla Model 3 is Arnold.
solver.add(car_model_vars[house] == car_model_map['tesla model 3'] for house in houses if solver.check() == sat)
solver.add(name_vars[house] == name_map['Arnold'] for house in houses if solver.check() == sat)

# 7. The person whose birthday is in February is the person who loves cooking.
solver.add(birthday_vars[house] == birthday_map['feb'] for house in houses if solver.check() == sat)
solver.add(hobby_vars[house] == hobby_map['cooking'] for house in houses if solver.check() == sat)

# 8. The person who owns a Toyota Camry is Peter.
solver.add(car_model_vars[house] == car_model_map['toyota camry'] for house in houses if solver.check() == sat)
solver.add(name_vars[house] == name_map['Peter'] for house in houses if solver.check() == sat)

# 9. The person whose birthday is in April is Arnold.
solver.add(birthday_vars[house] == birthday_map['april'] for house in houses if solver.check() == sat)
solver.add(name_vars[house] == name_map['Arnold'] for house in houses if solver.check() == sat)

# 10. Alice is the photography enthusiast.
solver.add(name_vars[house] == name_map['Alice'] for house in houses if solver.check() == sat)
solver.add(hobby_vars[house] == hobby_map['photography'] for house in houses if solver.check() == sat)

# 11. Peter is the person whose birthday is in January.
solver.add(name_vars[house] == name_map['Peter'] for house in houses if solver.check() == sat)
solver.add(birthday_vars[house] == birthday_map['jan'] for house in houses if solver.check() == sat)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        car_model = car_models[model[car_model_vars[house]].as_long()]
        birthday = birthdays[model[birthday_vars[house]].as_long()]
        hobby = hobbies[model[hobby_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, car_model, birthday, hobby])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")