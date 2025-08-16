from z3 import *

# Define variables
houses = [Int(f"house_{i}") for i in range(1, 7)]
names = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
car_models = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

# Create dictionaries for each attribute
name_vars = {name: Int(name) for name in names}
birthday_vars = {birthday: Int(birthday) for birthday in birthdays}
food_vars = {food: Int(food) for food in foods}
height_vars = {height: Int(height) for height in heights}
car_model_vars = {car_model: Int(car_model) for car_model in car_models}

# Create a solver instance
solver = Solver()

# Add constraints for each attribute to be in a unique house
solver.add(Distinct(houses))
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(birthday_vars.values()))
solver.add(Distinct(food_vars.values()))
solver.add(Distinct(height_vars.values()))
solver.add(Distinct(car_model_vars.values()))

# Map each attribute to a house
for name in names:
    solver.add(name_vars[name] >= 1)
    solver.add(name_vars[name] <= 6)

for birthday in birthdays:
    solver.add(birthday_vars[birthday] >= 1)
    solver.add(birthday_vars[birthday] <= 6)

for food in foods:
    solver.add(food_vars[food] >= 1)
    solver.add(food_vars[food] <= 6)

for height in heights:
    solver.add(height_vars[height] >= 1)
    solver.add(height_vars[height] <= 6)

for car_model in car_models:
    solver.add(car_model_vars[car_model] >= 1)
    solver.add(car_model_vars[car_model] <= 6)

# Add specific clues
# 1. The person who owns a Honda Civic is the person who is short.
solver.add(car_model_vars["honda civic"] == height_vars["short"])

# 2. The person who owns a Ford F-150 is in the fifth house.
solver.add(car_model_vars["ford f150"] == 5)

# 3. The person who loves stir fry is somewhere to the left of Eric.
solver.add(food_vars["stir fry"] < name_vars["Eric"])

# 4. The person whose birthday is in May is somewhere to the left of Carol.
solver.add(birthday_vars["may"] < name_vars["Carol"])

# 5. The person who is very short is somewhere to the left of the person whose birthday is in April.
solver.add(height_vars["very short"] < birthday_vars["april"])

# 6. The person who owns a BMW 3 Series is not in the third house.
solver.add(car_model_vars["bmw 3 series"] != 3)

# 7. There are two houses between the person who loves stir fry and the person who is a pizza lover.
solver.add(Abs(food_vars["stir fry"] - food_vars["pizza"]) == 3)

# 8. The person who loves the soup is directly left of Eric.
solver.add(food_vars["soup"] + 1 == name_vars["Eric"])

# 9. The person who loves the spaghetti eater and the person whose birthday is in May are next to each other.
solver.add(Abs(food_vars["spaghetti"] - birthday_vars["may"]) == 1)

# 10. Alice is directly left of the person who owns a BMW 3 Series.
solver.add(name_vars["Alice"] + 1 == car_model_vars["bmw 3 series"])

# 11. The person who owns a Tesla Model 3 is somewhere to the left of the person who is tall.
solver.add(car_model_vars["tesla model 3"] < height_vars["tall"])

# 12. The person who is very tall is the person who owns a Toyota Camry.
solver.add(height_vars["very tall"] == car_model_vars["toyota camry"])

# 13. Peter is directly left of the person who is a pizza lover.
solver.add(name_vars["Peter"] + 1 == food_vars["pizza"])

# 14. The person who loves the stew is not in the third house.
solver.add(food_vars["stew"] != 3)

# 15. There is one house between the person whose birthday is in September and the person who is very short.
solver.add(Abs(birthday_vars["sept"] - height_vars["very short"]) == 2)

# 16. There is one house between the person whose birthday is in March and the person who is super tall.
solver.add(Abs(birthday_vars["mar"] - height_vars["super tall"]) == 2)

# 17. The person who is tall is Bob.
solver.add(height_vars["tall"] == name_vars["Bob"])

# 18. The person whose birthday is in May is somewhere to the right of Alice.
solver.add(birthday_vars["may"] > name_vars["Alice"])

# 19. The person who is very short is in the fourth house.
solver.add(height_vars["very short"] == 4)

# 20. The person whose birthday is in March is the person who is short.
solver.add(birthday_vars["mar"] == height_vars["short"])

# 21. Carol is the person who owns a Tesla Model 3.
solver.add(name_vars["Carol"] == car_model_vars["tesla model 3"])

# 22. Eric is the person whose birthday is in January.
solver.add(name_vars["Eric"] == birthday_vars["jan"])

# Check if the solution is satisfiable
if solver.check() == sat:
    m = solver.model()
    solution = []
    for house in range(1, 7):
        name = [k for k, v in name_vars.items() if m[v] == house][0]
        birthday = [k for k, v in birthday_vars.items() if m[v] == house][0]
        food = [k for k, v in food_vars.items() if m[v] == house][0]
        height = [k for k, v in height_vars.items() if m[v] == house][0]
        car_model = [k for k, v in car_model_vars.items() if m[v] == house][0]
        solution.append([str(house), name, birthday, food, height, car_model])

    result = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": solution
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found")