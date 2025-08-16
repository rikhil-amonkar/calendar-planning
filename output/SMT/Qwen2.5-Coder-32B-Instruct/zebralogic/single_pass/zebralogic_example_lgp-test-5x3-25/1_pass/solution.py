from z3 import *

# Create Solver
solver = Solver()

# Define variables
names = ['Arnold', 'Bob', 'Alice', 'Eric', 'Peter']
heights = ['very tall', 'average', 'tall', 'very short', 'short']
foods = ['stew', 'grilled cheese', 'spaghetti', 'pizza', 'stir fry']
houses = [1, 2, 3, 4, 5]

# Declare variables
name_vars = {house: Int(f'name_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}
food_vars = {house: Int(f'food_{house}') for house in houses}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))
solver.add(Distinct([food_vars[house] for house in houses]))

# Map names, heights, and foods to integers
name_map = {name: i for i, name in enumerate(names)}
height_map = {height: i for i, height in enumerate(heights)}
food_map = {food: i for i, food in enumerate(foods)}

# Add clues as constraints
# 1. Alice is the person who is short.
solver.add(name_vars[houses[4]] == name_map['Alice'])
solver.add(height_vars[houses[4]] == height_map['short'])

# 2. The person who is tall is in the third house.
solver.add(height_vars[houses[2]] == height_map['tall'])

# 3. The person who has an average height is not in the second house.
solver.add(height_vars[houses[1]] != height_map['average'])

# 4. The person who has an average height is somewhere to the left of the person who loves the stew.
avg_height_house = Int('avg_height_house')
stew_house = Int('stew_house')
solver.add(Or([And(height_vars[house] == height_map['average'], avg_height_house == house) for house in houses]))
solver.add(Or([And(food_vars[house] == food_map['stew'], stew_house == house) for house in houses]))
solver.add(avg_height_house < stew_house)

# 5. The person who loves stir fry is Arnold.
solver.add(food_vars[houses[0]] == food_map['stir fry'])
solver.add(name_vars[houses[0]] == name_map['Arnold'])

# 6. The person who is a pizza lover is the person who is tall.
solver.add(food_vars[houses[2]] == food_map['pizza'])

# 7. Eric is the person who is tall.
solver.add(name_vars[houses[2]] == name_map['Eric'])

# 8. Bob is somewhere to the right of Arnold.
bob_house = Int('bob_house')
arnold_house = Int('arnold_house')
solver.add(Or([And(name_vars[house] == name_map['Bob'], bob_house == house) for house in houses]))
solver.add(Or([And(name_vars[house] == name_map['Arnold'], arnold_house == house) for house in houses]))
solver.add(bob_house > arnold_house)

# 9. The person who loves eating grilled cheese is somewhere to the right of Eric.
grilled_cheese_house = Int('grilled_cheese_house')
solver.add(Or([And(food_vars[house] == food_map['grilled cheese'], grilled_cheese_house == house) for house in houses]))
solver.add(grilled_cheese_house > houses[2])

# 10. The person who is very short is somewhere to the left of Arnold.
very_short_house = Int('very_short_house')
solver.add(Or([And(height_vars[house] == height_map['very short'], very_short_house == house) for house in houses]))
solver.add(very_short_house < arnold_house)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model.evaluate(name_vars[house])].as_long()]
        height = heights[model.evaluate(height_vars[house]).as_long()]
        food = foods[model.evaluate(food_vars[house]).as_long()]
        solution.append([str(house), name, height, food])
    
    print({
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": solution
        }
    })
else:
    print("No solution found")