from z3 import *

# Define the domains
names = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
car_models = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

# Create dictionaries to hold the variables
house_vars = {i: {"name": Int(f"name_{i}"),
                  "birthday": Int(f"birthday_{i}"),
                  "food": Int(f"food_{i}"),
                  "height": Int(f"height_{i}"),
                  "car_model": Int(f"car_model_{i}")}
              for i in range(1, 7)}

# Create solvers
solver = Solver()

# Add constraints for unique values per characteristic
for char in ["name", "birthday", "food", "height", "car_model"]:
    solver.add(Distinct([house_vars[i][char] for i in range(1, 7)]))

# Map values to integers
name_map = {name: i for i, name in enumerate(names)}
birthday_map = {birthday: i for i, birthday in enumerate(birthdays)}
food_map = {food: i for i, food in enumerate(foods)}
height_map = {height: i for i, height in enumerate(heights)}
car_model_map = {car_model: i for i, car_model in enumerate(car_models)}

# Encode the clues
# Clue 1
solver.add(house_vars[4]["car_model"] == car_model_map["honda civic"])
solver.add(house_vars[4]["height"] == height_map["short"])

# Clue 2
solver.add(house_vars[5]["car_model"] == car_model_map["ford f150"])

# Clue 3
solver.add(Or([house_vars[i]["food"] == food_map["stir fry"] for i in range(1, 5)]))

# Clue 4
solver.add(Or([house_vars[i]["birthday"] == birthday_map["may"] for i in range(1, 5)]))

# Clue 5
solver.add(Or([house_vars[i]["height"] == height_map["very short"] for i in range(1, 4)]))

# Clue 6
solver.add(house_vars[3]["car_model"] != car_model_map["bmw 3 series"])

# Clue 7
solver.add(Or([And(house_vars[i]["food"] == food_map["stir fry"], house_vars[i+2]["food"] == food_map["pizza"]) for i in range(1, 5)] +
              [And(house_vars[i+2]["food"] == food_map["stir fry"], house_vars[i]["food"] == food_map["pizza"]) for i in range(1, 5)]))

# Clue 8
solver.add(Or([house_vars[i]["food"] == food_map["soup"] for i in range(1, 5)]))
solver.add(Or([And(house_vars[i]["food"] == food_map["soup"], house_vars[i+1]["name"] == name_map["Eric"]) for i in range(1, 6)]))

# Clue 9
solver.add(Or([And(house_vars[i]["birthday"] == birthday_map["may"], house_vars[i+1]["food"] == food_map["spaghetti"]) for i in range(1, 6)] +
              [And(house_vars[i+1]["birthday"] == birthday_map["may"], house_vars[i]["food"] == food_map["spaghetti"]) for i in range(1, 6)]))

# Clue 10
solver.add(Or([house_vars[i]["name"] == name_map["Alice"] for i in range(1, 5)]))
solver.add(Or([And(house_vars[i]["name"] == name_map["Alice"], house_vars[i+1]["car_model"] == car_model_map["bmw 3 series"]) for i in range(1, 6)]))

# Clue 11
solver.add(Or([house_vars[i]["car_model"] == car_model_map["tesla model 3"] for i in range(1, 5)]))
solver.add(Or([And(house_vars[i]["car_model"] == car_model_map["tesla model 3"], house_vars[i+1]["height"] == height_map["tall"]) for i in range(1, 6)]))

# Clue 12
solver.add(house_vars[6]["car_model"] == car_model_map["toyota camry"])
solver.add(house_vars[6]["height"] == height_map["very tall"])

# Clue 13
solver.add(Or([house_vars[i]["name"] == name_map["Peter"] for i in range(1, 5)]))
solver.add(Or([And(house_vars[i]["name"] == name_map["Peter"], house_vars[i+1]["food"] == food_map["pizza"]) for i in range(1, 6)]))

# Clue 14
solver.add(house_vars[3]["food"] != food_map["stew"])

# Clue 15
solver.add(Or([And(house_vars[i]["birthday"] == birthday_map["sept"], house_vars[i+1]["height"] == height_map["very short"]) for i in range(1, 5)] +
              [And(house_vars[i+1]["birthday"] == birthday_map["sept"], house_vars[i]["height"] == height_map["very short"]) for i in range(1, 5)]))

# Clue 16
solver.add(Or([And(house_vars[i]["birthday"] == birthday_map["mar"], house_vars[i+1]["height"] == height_map["super tall"]) for i in range(1, 5)] +
              [And(house_vars[i+1]["birthday"] == birthday_map["mar"], house_vars[i]["height"] == height_map["super tall"]) for i in range(1, 5)]))

# Clue 17
solver.add(house_vars[6]["name"] == name_map["Bob"])
solver.add(house_vars[6]["height"] == height_map["tall"])

# Clue 18
solver.add(Or([house_vars[i]["birthday"] == birthday_map["may"] for i in range(2, 6)]))

# Clue 19
solver.add(house_vars[4]["birthday"] == birthday_map["may"])

# Clue 20
solver.add(house_vars[4]["height"] == height_map["short"])
solver.add(house_vars[4]["birthday"] == birthday_map["mar"])

# Clue 21
solver.add(house_vars[6]["car_model"] == car_model_map["tesla model 3"])
solver.add(house_vars[6]["name"] == name_map["Carol"])

# Clue 22
solver.add(house_vars[1]["name"] == name_map["Eric"])
solver.add(house_vars[1]["birthday"] == birthday_map["jan"])

# Solve the problem
if solver.check() == sat:
    m = solver.model()
    solution = []
    for i in range(1, 7):
        name_val = names[m.eval(house_vars[i]["name"]).as_long()]
        birthday_val = birthdays[m.eval(house_vars[i]["birthday"]).as_long()]
        food_val = foods[m.eval(house_vars[i]["food"]).as_long()]
        height_val = heights[m.eval(house_vars[i]["height"]).as_long()]
        car_model_val = car_models[m.eval(house_vars[i]["car_model"]).as_long()]
        solution.append([str(i), name_val, birthday_val, food_val, height_val, car_model_val])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")