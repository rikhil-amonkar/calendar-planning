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
solver.add(height_vars.index('tall') == mother_vars.index('Holly'))

# 2. There are two houses between the person who has an average height and the person who is short.
solver.add(Abs(height_vars.index('average') - height_vars.index('short')) == 3)

# 3. The person who has gray hair is directly left of The person whose mother's name is Janelle.
solver.add(hair_color_vars.index('gray') + 1 == mother_vars.index('Janelle'))

# 4. The person who has black hair is not in the fourth house.
solver.add(hair_color_vars[3] != hair_colors.index('black'))

# 5. Eric is the person who has black hair.
solver.add(name_vars[hair_color_vars.index('black')] == names.index('Eric'))

# 6. The person who is very short is The person whose mother's name is Penny.
solver.add(height_vars.index('very short') == mother_vars.index('Penny'))

# 7. Eric and the person who has gray hair are next to each other.
solver.add(Abs(name_vars.index('Eric') - hair_color_vars.index('gray')) == 1)

# 8. Bob is in the fifth house.
solver.add(name_vars[4] == names.index('Bob'))

# 9. The person who has red hair is Peter.
solver.add(name_vars[hair_color_vars.index('red')] == names.index('Peter'))

# 10. The person whose mother's name is Kailyn is directly left of the person who is short.
solver.add(mother_vars.index('Kailyn') + 1 == height_vars.index('short'))

# 11. Arnold is the person who has brown hair.
solver.add(name_vars[hair_color_vars.index('brown')] == names.index('Arnold'))

# 12. The person who has brown hair is somewhere to the left of The person whose mother's name is Janelle.
solver.add(hair_color_vars.index('brown') < mother_vars.index('Janelle'))

# 13. The person whose mother's name is Aniya and the person who is very short are next to each other.
solver.add(Abs(mother_vars.index('Aniya') - height_vars.index('very short')) == 1)

# 14. The person whose mother's name is Kailyn is in the third house.
solver.add(mother_vars[2] == mothers.index('Kailyn'))

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