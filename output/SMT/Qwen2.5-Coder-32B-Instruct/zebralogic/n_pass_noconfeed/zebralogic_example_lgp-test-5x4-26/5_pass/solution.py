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
solver.add(Exists([Int('i')], And(0 <= Int('i'), Int('i') < num_houses, height_vars[Int('i')] == tall_index, mother_vars[Int('i')] == holly_index)))

# 2. There are two houses between the person who has an average height and the person who is short.
average_index = heights.index('average')
short_index = heights.index('short')
solver.add(Exists([Int('i'), Int('j')], And(0 <= Int('i'), Int('i') < num_houses, 0 <= Int('j'), Int('j') < num_houses, Int('i') != Int('j'), Abs(Int('i') - Int('j')) == 3, height_vars[Int('i')] == average_index, height_vars[Int('j')] == short_index)))

# 3. The person who has gray hair is directly left of The person whose mother's name is Janelle.
gray_index = hair_colors.index('gray')
janelle_index = mothers.index('Janelle')
solver.add(Exists([Int('i')], And(0 <= Int('i'), Int('i') < num_houses - 1, hair_color_vars[Int('i')] == gray_index, mother_vars[Int('i') + 1] == janelle_index)))

# 4. The person who has black hair is not in the fourth house.
black_index = hair_colors.index('black')
solver.add(hair_color_vars[3] != black_index)

# 5. Eric is the person who has black hair.
eric_index = names.index('Eric')
solver.add(Exists([Int('i')], And(0 <= Int('i'), Int('i') < num_houses, name_vars[Int('i')] == eric_index, hair_color_vars[Int('i')] == black_index)))

# 6. The person who is very short is The person whose mother's name is Penny.
very_short_index = heights.index('very short')
penny_index = mothers.index('Penny')
solver.add(Exists([Int('i')], And(0 <= Int('i'), Int('i') < num_houses, height_vars[Int('i')] == very_short_index, mother_vars[Int('i')] == penny_index)))

# 7. Eric and the person who has gray hair are next to each other.
solver.add(Exists([Int('i'), Int('j')], And(0 <= Int('i'), Int('i') < num_houses, 0 <= Int('j'), Int('j') < num_houses, Int('i') != Int('j'), Abs(Int('i') - Int('j')) == 1, name_vars[Int('i')] == eric_index, hair_color_vars[Int('j')] == gray_index)))

# 8. Bob is in the fifth house.
bob_index = names.index('Bob')
solver.add(name_vars[4] == bob_index)

# 9. The person who has red hair is Peter.
peter_index = names.index('Peter')
red_index = hair_colors.index('red')
solver.add(Exists([Int('i')], And(0 <= Int('i'), Int('i') < num_houses, name_vars[Int('i')] == peter_index, hair_color_vars[Int('i')] == red_index)))

# 10. The person whose mother's name is Kailyn is directly left of the person who is short.
kailyn_index = mothers.index('Kailyn')
solver.add(Exists([Int('i')], And(0 <= Int('i'), Int('i') < num_houses - 1, mother_vars[Int('i')] == kailyn_index, height_vars[Int('i') + 1] == short_index)))

# 11. Arnold is the person who has brown hair.
arnold_index = names.index('Arnold')
brown_index = hair_colors.index('brown')
solver.add(Exists([Int('i')], And(0 <= Int('i'), Int('i') < num_houses, name_vars[Int('i')] == arnold_index, hair_color_vars[Int('i')] == brown_index)))

# 12. The person who has brown hair is somewhere to the left of The person whose mother's name is Janelle.
solver.add(Exists([Int('i'), Int('j')], And(0 <= Int('i'), Int('i') < num_houses, 0 <= Int('j'), Int('j') < num_houses, Int('i') < Int('j'), hair_color_vars[Int('i')] == brown_index, mother_vars[Int('j')] == janelle_index)))

# 13. The person whose mother's name is Aniya and the person who is very short are next to each other.
aniya_index = mothers.index('Aniya')
solver.add(Exists([Int('i'), Int('j')], And(0 <= Int('i'), Int('i') < num_houses, 0 <= Int('j'), Int('j') < num_houses, Int('i') != Int('j'), Abs(Int('i') - Int('j')) == 1, mother_vars[Int('i')] == aniya_index, height_vars[Int('j')] == very_short_index)))

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