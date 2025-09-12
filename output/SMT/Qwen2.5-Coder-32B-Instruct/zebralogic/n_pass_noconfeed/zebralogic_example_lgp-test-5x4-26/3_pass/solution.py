from z3 import *

# Define the number of houses
num_houses = 5

# Define the domains for each attribute
names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
heights = ['very short', 'short', 'tall', 'average', 'very tall']
mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']

# Create arrays to map houses to attributes
name_vars = [Int(f'name_house_{i+1}') for i in range(num_houses)]
height_vars = [Int(f'height_house_{i+1}') for i in range(num_houses)]
mother_vars = [Int(f'mother_house_{i+1}') for i in range(num_houses)]
hair_color_vars = [Int(f'hair_color_house_{i+1}') for i in range(num_houses)]

# Create a solver instance
solver = Solver()

# Add constraints for unique values for each attribute
solver.add(Distinct(name_vars))
solver.add(Distinct(height_vars))
solver.add(Distinct(mother_vars))
solver.add(Distinct(hair_color_vars))

# Map each attribute to its possible values
for i in range(num_houses):
    solver.add(Or([name_vars[i] == j for j in range(len(names))]))
    solver.add(Or([height_vars[i] == j for j in range(len(heights))]))
    solver.add(Or([mother_vars[i] == j for j in range(len(mothers))]))
    solver.add(Or([hair_color_vars[i] == j for j in range(len(hair_colors))]))

# Add constraints for each clue
# 1. The person who is tall is The person whose mother's name is Holly.
tall_index = heights.index('tall')
holly_index = mothers.index('Holly')
solver.add(Or([And(height_vars[i] == tall_index, mother_vars[i] == holly_index) for i in range(num_houses)]))

# 2. There are two houses between the person who has an average height and the person who is short.
average_index = heights.index('average')
short_index = heights.index('short')
solver.add(Or([Abs(height_vars[i] - height_vars[j]) == 3 for i in range(num_houses) for j in range(num_houses) if i != j and height_vars[i] == average_index and height_vars[j] == short_index]))

# 3. The person who has gray hair is directly left of The person whose mother's name is Janelle.
gray_index = hair_colors.index('gray')
janelle_index = mothers.index('Janelle')
solver.add(Or([And(hair_color_vars[i] == gray_index, mother_vars[i+1] == janelle_index) for i in range(num_houses - 1)]))

# 4. The person who has black hair is not in the fourth house.
black_index = hair_colors.index('black')
solver.add(hair_color_vars[3] != black_index)

# 5. Eric is the person who has black hair.
eric_index = names.index('Eric')
solver.add(Or([And(name_vars[i] == eric_index, hair_color_vars[i] == black_index) for i in range(num_houses)]))

# 6. The person who is very short is The person whose mother's name is Penny.
very_short_index = heights.index('very short')
penny_index = mothers.index('Penny')
solver.add(Or([And(height_vars[i] == very_short_index, mother_vars[i] == penny_index) for i in range(num_houses)]))

# 7. Eric and the person who has gray hair are next to each other.
solver.add(Or([Abs(name_vars[i] - hair_color_vars[j]) == 1 for i in range(num_houses) for j in range(num_houses) if i != j and name_vars[i] == eric_index and hair_color_vars[j] == gray_index]))

# 8. Bob is in the fifth house.
bob_index = names.index('Bob')
solver.add(name_vars[4] == bob_index)

# 9. The person who has red hair is Peter.
peter_index = names.index('Peter')
red_index = hair_colors.index('red')
solver.add(Or([And(name_vars[i] == peter_index, hair_color_vars[i] == red_index) for i in range(num_houses)]))

# 10. The person whose mother's name is Kailyn is directly left of the person who is short.
kailyn_index = mothers.index('Kailyn')
solver.add(Or([And(mother_vars[i] == kailyn_index, height_vars[i+1] == short_index) for i in range(num_houses - 1)]))

# 11. Arnold is the person who has brown hair.
arnold_index = names.index('Arnold')
brown_index = hair_colors.index('brown')
solver.add(Or([And(name_vars[i] == arnold_index, hair_color_vars[i] == brown_index) for i in range(num_houses)]))

# 12. The person who has brown hair is somewhere to the left of The person whose mother's name is Janelle.
solver.add(Or([And(hair_color_vars[i] == brown_index, mother_vars[j] == janelle_index) for i in range(num_houses) for j in range(i + 1, num_houses)]))

# 13. The person whose mother's name is Aniya and the person who is very short are next to each other.
aniya_index = mothers.index('Aniya')
solver.add(Or([Abs(mother_vars[i] - height_vars[j]) == 1 for i in range(num_houses) for j in range(num_houses) if i != j and mother_vars[i] == aniya_index and height_vars[j] == very_short_index]))

# 14. The person whose mother's name is Kailyn is in the third house.
solver.add(mother_vars[2] == kailyn_index)

# Solve the puzzle
if solver.check() == sat:
    model = solver.model()
    # Extract the solution
    solution = []
    for house in range(num_houses):
        name = names[model.evaluate(name_vars[house]).as_long()]
        height = heights[model.evaluate(height_vars[house]).as_long()]
        mother = mothers[model.evaluate(mother_vars[house]).as_long()]
        hair_color = hair_colors[model.evaluate(hair_color_vars[house]).as_long()]
        solution.append([str(house + 1), name, height, mother, hair_color])
    
    # Format the solution as JSON
    import json
    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": solution
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found")