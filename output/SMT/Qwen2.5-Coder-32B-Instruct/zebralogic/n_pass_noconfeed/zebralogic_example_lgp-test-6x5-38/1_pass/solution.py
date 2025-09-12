from z3 import *

# Define the domains
names = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
car_models = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

# Create a solver instance
solver = Solver()

# Create variables
house_vars = [Int(f"house_{i}") for i in range(1, 7)]
name_vars = {name: Int(f"name_{name}") for name in names}
birthday_vars = {birthday: Int(f"birthday_{birthday}") for birthday in birthdays}
food_vars = {food: Int(f"food_{food}") for food in foods}
height_vars = {height: Int(f"height_{height}") for height in heights}
car_model_vars = {car_model: Int(f"car_model_{car_model}") for car_model in car_models}

# Add domain constraints
for var_list in [house_vars, list(name_vars.values()), list(birthday_vars.values()), list(food_vars.values()), list(height_vars.values()), list(car_model_vars.values())]:
    solver.add(Distinct(var_list))
    for var in var_list:
        solver.add(var >= 1)
        solver.add(var <= 6)

# Add specific constraints
solver.add(car_model_vars["honda civic"] == height_vars["short"])
solver.add(car_model_vars["ford f150"] == 5)
solver.add(food_vars["stir fry"] < name_vars["Eric"])
solver.add(birthday_vars["may"] < name_vars["Carol"])
solver.add(height_vars["very short"] < birthday_vars["april"])
solver.add(car_model_vars["bmw 3 series"] != 3)
solver.add(Abs(food_vars["stir fry"] - food_vars["pizza"]) == 2)
solver.add(food_vars["soup"] + 1 == name_vars["Eric"])
solver.add(Abs(food_vars["spaghetti"] - birthday_vars["may"]) == 1)
solver.add(name_vars["Alice"] + 1 == car_model_vars["bmw 3 series"])
solver.add(car_model_vars["tesla model 3"] < height_vars["tall"])
solver.add(height_vars["very tall"] == car_model_vars["toyota camry"])
solver.add(name_vars["Peter"] + 1 == food_vars["pizza"])
solver.add(food_vars["stew"] != 3)
solver.add(Abs(birthday_vars["sept"] - height_vars["very short"]) == 1)
solver.add(Abs(birthday_vars["mar"] - height_vars["super tall"]) == 1)
solver.add(height_vars["tall"] == name_vars["Bob"])
solver.add(birthday_vars["may"] > name_vars["Alice"])
solver.add(height_vars["very short"] == 4)
solver.add(birthday_vars["mar"] == height_vars["short"])
solver.add(name_vars["Carol"] == car_model_vars["tesla model 3"])
solver.add(name_vars["Eric"] == birthday_vars["jan"])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    # Prepare the solution
    solution = {"solution": {"header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"], "rows": []}}
    for house in range(1, 7):
        row = [str(house)]
        for d, vars_dict in zip(["Name", "Birthday", "Food", "Height", "CarModel"], [name_vars, birthday_vars, food_vars, height_vars, car_model_vars]):
            for key, value in vars_dict.items():
                if model.evaluate(value) == house:
                    row.append(key)
        solution["solution"]["rows"].append(row)
    import json
    print(json.dumps(solution))
else:
    print("No solution found")