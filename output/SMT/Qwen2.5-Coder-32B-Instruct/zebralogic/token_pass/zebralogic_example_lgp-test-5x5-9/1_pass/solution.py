from z3 import *

# Define the domains
names = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
drinks = ['milk', 'root beer', 'coffee', 'tea', 'water']
colors = ['blue', 'green', 'white', 'yellow', 'red']
flowers = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
hobbies = ['painting', 'cooking', 'photography', 'gardening', 'knitting']

# Create variables
house_vars = [Int(f'house_{i}') for i in range(1, 6)]
name_vars = [String(f'name_{i}') for i in range(1, 6)]
drink_vars = [String(f'drink_{i}') for i in range(1, 6)]
color_vars = [String(f'color_{i}') for i in range(1, 6)]
flower_vars = [String(f'flower_{i}') for i in range(1, 6)]
hobby_vars = [String(f'hobby_{i}') for i in range(1, 6)]

# Create solver instance
solver = Solver()

# Add constraints for unique values in each category
solver.add(Distinct(name_vars))
solver.add(Distinct(drink_vars))
solver.add(Distinct(color_vars))
solver.add(Distinct(flower_vars))
solver.add(Distinct(hobby_vars))

# Add constraints for each house number
for i in range(1, 6):
    solver.add(house_vars[i-1] == i)

# Clue 1: Alice is not in the fourth house.
solver.add(name_vars[3] != 'Alice')

# Clue 2: The root beer lover is the person who enjoys gardening.
solver.add(And([drink_vars[i] == 'root beer' == hobby_vars[i] for i in range(5)]))

# Clue 3: The person whose favorite color is green is the coffee drinker.
solver.add(And([color_vars[i] == 'green' == drink_vars[i] for i in range(5)]))

# Clue 4: The person whose favorite color is green is the person who loves the bouquet of lilies.
solver.add(And([color_vars[i] == 'green' == flower_vars[i] for i in range(5)]))

# Clue 5: The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils.
solver.add(Or([And(flower_vars[i] == 'daffodils', color_vars[j] == 'blue') for i in range(5) for j in range(i+1, 5)]))

# Clue 6: The person who loves cooking is the person who loves blue.
solver.add(And([color_vars[i] == 'blue' == hobby_vars[i] for i in range(5)]))

# Clue 7: Eric is directly left of the tea drinker.
solver.add(Or([And(name_vars[i] == 'Eric', drink_vars[i+1] == 'tea') for i in range(4)]))

# Clue 8: The one who only drinks water is Peter.
solver.add(drink_vars[2] == 'water')
solver.add(name_vars[2] == 'Peter')

# Clue 9: Arnold is the photography enthusiast.
solver.add(And([name_vars[i] == 'Arnold' == hobby_vars[i] for i in range(5)]))

# Clue 10: The person who loves white is the person who loves the rose bouquet.
solver.add(And([color_vars[i] == 'white' == flower_vars[i] for i in range(5)]))

# Clue 11: There is one house between the person who loves a carnations arrangement and the person whose favorite color is red.
solver.add(Or([And(flower_vars[i] == 'carnations', color_vars[i+2] == 'red') for i in range(3)] + 
              [And(flower_vars[i] == 'carnations', color_vars[i-2] == 'red') for i in range(2, 5)]))

# Clue 12: The person who loves cooking is somewhere to the left of the person who paints as a hobby.
solver.add(Or([And(hobby_vars[i] == 'cooking', hobby_vars[j] == 'painting') for i in range(5) for j in range(i+1, 5)]))

# Clue 13: The one who only drinks water is in the third house.
solver.add(drink_vars[2] == 'water')

# Clue 14: The person who loves a carnations arrangement is the root beer lover.
solver.add(And([flower_vars[i] == 'carnations' == drink_vars[i] for i in range(5)]))

# Clue 15: The person who loves white is in the second house.
solver.add(color_vars[1] == 'white')

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(1, 6):
        house = str(i)
        name = model[name_vars[i-1]].as_string().strip('"')
        drink = model[drink_vars[i-1]].as_string().strip('"')
        color = model[color_vars[i-1]].as_string().strip('"')
        flower = model[flower_vars[i-1]].as_string().strip('"')
        hobby = model[hobby_vars[i-1]].as_string().strip('"')
        solution.append([house, name, drink, color, flower, hobby])
    
    # Format the solution as JSON
    result = {
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")