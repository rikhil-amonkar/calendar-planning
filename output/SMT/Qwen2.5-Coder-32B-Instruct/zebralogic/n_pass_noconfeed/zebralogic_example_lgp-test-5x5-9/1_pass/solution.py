from z3 import *

# Define the variables
names = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
drinks = ["milk", "root beer", "coffee", "tea", "water"]
colors = ["blue", "green", "white", "yellow", "red"]
flowers = ["daffodils", "roses", "lilies", "tulips", "carnations"]
hobbies = ["painting", "cooking", "photography", "gardening", "knitting"]

houses = range(1, 6)

name_vars = {house: Int(f"name_{house}") for house in houses}
drink_vars = {house: Int(f"drink_{house}") for house in houses}
color_vars = {house: Int(f"color_{house}") for house in houses}
flower_vars = {house: Int(f"flower_{house}") for house in houses}
hobby_vars = {house: Int(f"hobby_{house}") for house in houses}

# Create the solver
solver = Solver()

# Add constraints for unique values in each category
for category_vars in [name_vars, drink_vars, color_vars, flower_vars, hobby_vars]:
    solver.add(Distinct(category_vars.values()))

# Map names to integers
name_map = {name: i for i, name in enumerate(names)}
drink_map = {drink: i for i, drink in enumerate(drinks)}
color_map = {color: i for i, color in enumerate(colors)}
flower_map = {flower: i for i, flower in enumerate(flowers)}
hobby_map = {hobby: i for i, hobby in enumerate(hobbies)}

# Add specific constraints
solver.add(name_vars[4] != name_map["Alice"])  # Clue 1
solver.add(drink_vars[i] == drink_map["root beer"] == hobby_vars[i] == hobby_map["gardening"] for i in houses)  # Clue 2
solver.add(color_vars[i] == color_map["green"] == drink_vars[i] == drink_map["coffee"] for i in houses)  # Clue 3
solver.add(color_vars[i] == color_map["green"] == flower_vars[i] == flower_map["lilies"] for i in houses)  # Clue 4
solver.add(Or([And(color_vars[j] == color_map["blue"], color_vars[i] == color_map["daffodils"]) for i in range(1, 5) for j in range(i+1, 6)]))  # Clue 5
solver.add(hobby_vars[i] == hobby_map["cooking"] == color_vars[i] == color_map["blue"] for i in houses)  # Clue 6
solver.add(name_vars[i] == name_map["Eric"] == drink_vars[i+1] == drink_map["tea"] for i in range(1, 5))  # Clue 7
solver.add(name_vars[3] == name_map["Peter"] == drink_vars[3] == drink_map["water"])  # Clue 8 & 13
solver.add(hobby_vars[i] == hobby_map["photography"] == name_vars[i] == name_map["Arnold"] for i in houses)  # Clue 9
solver.add(color_vars[2] == color_map["white"] == flower_vars[2] == flower_map["roses"])  # Clue 10 & 15
solver.add(Or([And(flower_vars[i] == flower_map["carnations"], color_vars[j] == color_map["red"]) for i in range(1, 4) for j in [i+2, i-2] if 1 <= j <= 5]))  # Clue 11
solver.add(Or([And(hobby_vars[i] == hobby_map["cooking"], hobby_vars[j] == hobby_map["painting"]) for i in range(1, 5) for j in range(i+1, 6)]))  # Clue 12
solver.add(drink_vars[3] == drink_map["water"])  # Clue 13
solver.add(drink_vars[i] == drink_map["root beer"] == flower_vars[i] == flower_map["carnations"] for i in houses)  # Clue 14

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        drink = drinks[model.evaluate(drink_vars[house]).as_long()]
        color = colors[model.evaluate(color_vars[house]).as_long()]
        flower = flowers[model.evaluate(flower_vars[house]).as_long()]
        hobby = hobbies[model.evaluate(hobby_vars[house]).as_long()]
        solution.append([str(house), name, drink, color, flower, hobby])
    
    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": solution
        }
    }))
else:
    print("No solution found")