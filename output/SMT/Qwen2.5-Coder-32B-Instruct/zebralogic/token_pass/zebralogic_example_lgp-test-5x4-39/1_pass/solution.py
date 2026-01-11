from z3 import *

# Define the solver
solver = Solver()

# Define the variables
names = ['Arnold', 'Peter', 'Eric', 'Alice', 'Bob']
hobbies = ['painting', 'cooking', 'knitting', 'gardening', 'photography']
heights = ['very tall', 'tall', 'very short', 'average', 'short']
foods = ['stew', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']

# Create dictionaries to hold the variables
name_vars = {house: Int(f'name_{house}') for house in range(1, 6)}
hobby_vars = {house: Int(f'hobby_{house}') for house in range(1, 6)}
height_vars = {house: Int(f'height_{house}') for house in range(1, 6)}
food_vars = {house: Int(f'food_{house}') for house in range(1, 6)}

# Map the names, hobbies, heights, and foods to integers
name_map = {name: i for i, name in enumerate(names)}
hobby_map = {hobby: i for i, hobby in enumerate(hobbies)}
height_map = {height: i for i, height in enumerate(heights)}
food_map = {food: i for i, food in enumerate(foods)}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in range(1, 6)]))
solver.add(Distinct([hobby_vars[house] for house in range(1, 6)]))
solver.add(Distinct([height_vars[house] for house in range(1, 6)]))
solver.add(Distinct([food_vars[house] for house in range(1, 6)]))

# Add constraints based on the clues
# Bob is the photography enthusiast
solver.add(hobby_vars[name_map['Bob'] + 1] == hobby_map['photography'])

# The person who loves eating grilled cheese is the person who is tall
solver.add(food_vars[height_map['tall'] + 1] == food_map['grilled cheese'])

# Peter is not in the second house
solver.add(name_vars[2] != name_map['Peter'])

# The person who is tall is directly left of the person who loves stir fry
solver.add(food_vars[height_map['tall'] + 2] == food_map['stir fry'])

# The person who loves cooking is the person who has an average height
solver.add(hobby_vars[height_map['average'] + 1] == hobby_map['cooking'])

# Alice is directly left of the person who is a pizza lover
solver.add(food_vars[name_map['Alice'] + 2] == food_map['pizza'])

# The person who loves spaghetti is not in the second house
solver.add(food_vars[2] != food_map['spaghetti'])

# Eric is not in the fifth house
solver.add(name_vars[5] != name_map['Eric'])

# The person who is short is Peter
solver.add(height_vars[name_map['Peter'] + 1] == height_map['short'])

# The person who has an average height and the person who enjoys gardening are next to each other
solver.add(Or(
    And(height_vars[hobby_map['gardening'] + 1] == height_map['average'] - 1,
        height_vars[hobby_map['gardening'] + 2] == height_map['average']),
    And(height_vars[hobby_map['gardening'] + 1] == height_map['average'],
        height_vars[hobby_map['gardening'] + 2] == height_map['average'] + 1)
))

# The person who paints as a hobby is directly left of the person who loves eating grilled cheese
solver.add(food_vars[hobby_map['painting'] + 2] == food_map['grilled cheese'])

# The person who is very short is in the fifth house
solver.add(height_vars[5] == height_map['very short'])

# The person who is tall is in the third house
solver.add(height_vars[3] == height_map['tall'])

# Alice is somewhere to the right of the photography enthusiast
solver.add(name_vars[name_map['Bob'] + 1] < name_vars[name_map['Alice'] + 1])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in range(1, 6):
        name = names[model.evaluate(name_vars[house]).as_long()]
        hobby = hobbies[model.evaluate(hobby_vars[house]).as_long()]
        height = heights[model.evaluate(height_vars[house]).as_long()]
        food = foods[model.evaluate(food_vars[house]).as_long()]
        solution.append([str(house), name, hobby, height, food])
    
    print({
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": solution
        }
    })
else:
    print("No solution found")