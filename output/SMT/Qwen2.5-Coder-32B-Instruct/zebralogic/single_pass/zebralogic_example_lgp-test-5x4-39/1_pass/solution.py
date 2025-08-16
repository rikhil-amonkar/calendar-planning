from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3, 4, 5]
names = ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob']
hobbies = ['painting', 'cooking', 'knitting', 'gardening', 'photography']
heights = ['very tall', 'tall', 'very short', 'average', 'short']
foods = ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']

# Create dictionaries to map variables to Z3 variables
name_vars = {house: Int(f'name_{house}') for house in houses}
hobby_vars = {house: Int(f'hobby_{house}') for house in houses}
height_vars = {house: Int(f'height_{house}') for house in houses}
food_vars = {house: Int(f'food_{house}') for house in houses}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([hobby_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))
solver.add(Distinct([food_vars[house] for house in houses]))

# Map values to integers
name_map = {name: i for i, name in enumerate(names)}
hobby_map = {hobby: i for i, hobby in enumerate(hobbies)}
height_map = {height: i for i, height in enumerate(heights)}
food_map = {food: i for i, food in enumerate(foods)}

# Add clues as constraints
# 1. Bob is the photography enthusiast.
solver.add(name_vars[houses[-1]] == name_map['Bob'])
solver.add(hobby_vars[houses[-1]] == hobby_map['photography'])

# 2. The person who loves eating grilled cheese is the person who is tall.
solver.add(And([Implies(food_vars[house] == food_map['grilled cheese'], height_vars[house] == height_map['tall']) for house in houses]))

# 3. Peter is not in the second house.
solver.add(name_vars[2] != name_map['Peter'])

# 4. The person who is tall is directly left of the person who loves stir fry.
solver.add(And([Implies(height_vars[house] == height_map['tall'], food_vars[house + 1] == food_map['stir fry']) for house in houses if house < 5]))

# 5. The person who loves cooking is the person who has an average height.
solver.add(And([Implies(hobby_vars[house] == hobby_map['cooking'], height_vars[house] == height_map['average']) for house in houses]))

# 6. Alice is directly left of the person who is a pizza lover.
solver.add(And([Implies(name_vars[house] == name_map['Alice'], food_vars[house + 1] == food_map['pizza']) for house in houses if house < 5]))

# 7. The person who loves the spaghetti eater is not in the second house.
solver.add(food_vars[2] != food_map['spaghetti'])

# 8. Eric is not in the fifth house.
solver.add(name_vars[5] != name_map['Eric'])

# 9. The person who is short is Peter.
solver.add(And([Implies(name_vars[house] == name_map['Peter'], height_vars[house] == height_map['short']) for house in houses]))

# 10. The person who has an average height and the person who enjoys gardening are next to each other.
solver.add(Or(
    And(height_vars[1] == height_map['average'], hobby_vars[2] == hobby_map['gardening']),
    And(height_vars[2] == height_map['average'], hobby_vars[1] == hobby_map['gardening']),
    And(height_vars[2] == height_map['average'], hobby_vars[3] == hobby_map['gardening']),
    And(height_vars[3] == height_map['average'], hobby_vars[2] == hobby_map['gardening']),
    And(height_vars[3] == height_map['average'], hobby_vars[4] == hobby_map['gardening']),
    And(height_vars[4] == height_map['average'], hobby_vars[3] == hobby_map['gardening']),
    And(height_vars[4] == height_map['average'], hobby_vars[5] == hobby_map['gardening']),
    And(height_vars[5] == height_map['average'], hobby_vars[4] == hobby_map['gardening'])
))

# 11. The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
solver.add(And([Implies(hobby_vars[house] == hobby_map['painting'], food_vars[house + 1] == food_map['grilled cheese']) for house in houses if house < 5]))

# 12. The person who is very short is in the fifth house.
solver.add(height_vars[5] == height_map['very short'])

# 13. The person who is tall is in the third house.
solver.add(height_vars[3] == height_map['tall'])

# 14. Alice is somewhere to the right of the photography enthusiast.
solver.add(Or(
    And(name_vars[2] == name_map['Bob'], name_vars[3] == name_map['Alice']),
    And(name_vars[2] == name_map['Bob'], name_vars[4] == name_map['Alice']),
    And(name_vars[2] == name_map['Bob'], name_vars[5] == name_map['Alice']),
    And(name_vars[3] == name_map['Bob'], name_vars[4] == name_map['Alice']),
    And(name_vars[3] == name_map['Bob'], name_vars[5] == name_map['Alice']),
    And(name_vars[4] == name_map['Bob'], name_vars[5] == name_map['Alice'])
))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        hobby = hobbies[model[hobby_vars[house]].as_long()]
        height = heights[model[height_vars[house]].as_long()]
        food = foods[model[food_vars[house]].as_long()]
        solution.append([str(house), name, hobby, height, food])
    
    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")