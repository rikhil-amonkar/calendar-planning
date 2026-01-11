from z3 import *

# Define domains
names = ["Eric", "Peter", "Alice", "Arnold"]
car_models = ["tesla model 3", "honda civic", "toyota camry", "ford f150"]
birthdays = ["jan", "april", "sept", "feb"]
hobbies = ["painting", "cooking", "gardening", "photography"]

# Create variables for each house
house_vars = []
for i in range(4):
    house_vars.append({
        "name": Int(f"name_{i+1}"),
        "car_model": Int(f"car_model_{i+1}"),
        "birthday": Int(f"birthday_{i+1}"),
        "hobby": Int(f"hobby_{i+1}")
    })

# Create solvers and add constraints
solver = Solver()

# Add domain constraints
for i in range(4):
    solver.add(house_vars[i]["name"] >= 0)
    solver.add(house_vars[i]["name"] <= 3)
    solver.add(house_vars[i]["car_model"] >= 0)
    solver.add(house_vars[i]["car_model"] <= 3)
    solver.add(house_vars[i]["birthday"] >= 0)
    solver.add(house_vars[i]["birthday"] <= 3)
    solver.add(house_vars[i]["hobby"] >= 0)
    solver.add(house_vars[i]["hobby"] <= 3)

# Add uniqueness constraints
for attr in ["name", "car_model", "birthday", "hobby"]:
    solver.add(Distinct([house_vars[i][attr] for i in range(4)]))

# Add clue constraints
# Clue 1: The person whose birthday is in January is not in the second house.
solver.add(house_vars[1]["birthday"] != birthdays.index("jan"))

# Clue 2 & 3: The photography enthusiast is somewhere to the left of Eric and Peter.
alice_house = house_vars[0]["name"] == names.index("Alice")
eric_house = house_vars[0]["name"] == names.index("Eric")
peter_house = house_vars[0]["name"] == names.index("Peter")
for i in range(3):
    solver.add(Implies(alice_house, house_vars[i]["hobby"] == hobbies.index("photography")))
    solver.add(Implies(eric_house, house_vars[i]["name"] == names.index("Eric")))
    solver.add(Implies(peter_house, house_vars[i]["name"] == names.index("Peter")))

# Clue 4: The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
honda_civic_index = car_models.index("honda civic")
tesla_model_3_index = car_models.index("tesla model 3")
for i in range(3):
    solver.add(Implies(house_vars[i]["car_model"] == honda_civic_index, house_vars[i+1]["car_model"] == tesla_model_3_index))

# Clue 5: There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
gardening_index = hobbies.index("gardening")
for i in range(3):
    solver.add(Or(
        And(house_vars[i]["car_model"] == tesla_model_3_index, house_vars[i+2]["hobby"] == gardening_index),
        And(house_vars[i+2]["car_model"] == tesla_model_3_index, house_vars[i]["hobby"] == gardening_index)
    ))

# Clue 6: The person who owns a Tesla Model 3 is Arnold.
arnold_index = names.index("Arnold")
solver.add(house_vars[i]["car_model"] == tesla_model_3_index == arnold_index)

# Clue 7: The person whose birthday is in February is the person who loves cooking.
february_index = birthdays.index("feb")
cooking_index = hobbies.index("cooking")
solver.add(And(house_vars[i]["birthday"] == february_index, house_vars[i]["hobby"] == cooking_index))

# Clue 8: The person who owns a Toyota Camry is Peter.
toyota_camry_index = car_models.index("toyota camry")
solver.add(house_vars[i]["car_model"] == toyota_camry_index == peter_house)

# Clue 9: The person whose birthday is in April is Arnold.
april_index = birthdays.index("april")
solver.add(And(house_vars[i]["birthday"] == april_index, house_vars[i]["name"] == arnold_index))

# Clue 10: Alice is the photography enthusiast.
alice_index = names.index("Alice")
solver.add(house_vars[i]["name"] == alice_index == house_vars[i]["hobby"] == photography_index)

# Clue 11: Peter is the person whose birthday is in January.
january_index = birthdays.index("jan")
solver.add(And(house_vars[i]["birthday"] == january_index, house_vars[i]["name"] == peter_house))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
            "rows": []
        }
    }
    for i in range(4):
        name = names[model.eval(house_vars[i]["name"]).as_long()]
        car_model = car_models[model.eval(house_vars[i]["car_model"]).as_long()]
        birthday = birthdays[model.eval(house_vars[i]["birthday"]).as_long()]
        hobby = hobbies[model.eval(house_vars[i]["hobby"]).as_long()]
        solution["solution"]["rows"].append([str(i+1), name, car_model, birthday, hobby])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")