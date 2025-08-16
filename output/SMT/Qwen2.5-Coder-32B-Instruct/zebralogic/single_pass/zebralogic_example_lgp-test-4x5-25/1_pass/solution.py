from z3 import *

# Define variables
names = ['Arnold', 'Peter', 'Eric', 'Alice']
house_styles = ['craftsman', 'colonial', 'victorian', 'ranch']
hair_colors = ['red', 'blonde', 'black', 'brown']
children = ['Bella', 'Fred', 'Meredith', 'Samantha']
book_genres = ['mystery', 'fantasy', 'romance', 'science fiction']

# Create Z3 variables
name_vars = [String(f'name_{i}') for i in range(4)]
house_style_vars = [String(f'house_style_{i}') for i in range(4)]
hair_color_vars = [String(f'hair_color_{i}') for i in range(4)]
child_vars = [String(f'child_{i}') for i in range(4)]
book_genre_vars = [String(f'book_genre_{i}') for i in range(4)]

solver = Solver()

# Add constraints based on clues
# Clue 1
solver.add(house_style_vars[2] == 'craftsman')

# Clue 2
solver.add(book_genre_vars[names.index('Alice')] == 'romance')

# Clue 3
solver.add(hair_color_vars[3] == 'brown')

# Clue 4
solver.add(child_vars[3] == 'Samantha')

# Clue 5
red_hair_index = Int('red_hair_index')
ranch_index = Int('ranch_index')
solver.add(Or([hair_color_vars[i] == 'red' for i in range(4)]))
solver.add(Or([house_style_vars[i] == 'ranch' for i in range(4)]))
solver.add(red_hair_index >= 0)
solver.add(red_hair_index < 4)
solver.add(ranch_index >= 0)
solver.add(ranch_index < 4)
solver.add(hair_color_vars[red_hair_index] == 'red')
solver.add(house_style_vars[ranch_index] == 'ranch')
solver.add(ranch_index > red_hair_index)

# Clue 6
solver.add(child_vars[names.index('Peter')] == 'Bella')

# Clue 7
solver.add(hair_color_vars[names.index('Arnold')] == 'red')

# Clue 8
solver.add(house_style_vars[names.index('Alice')] == 'colonial')

# Clue 9
solver.add(hair_color_vars[1] == 'black')

# Clue 10
solver.add(book_genre_vars[names.index('Peter')] == 'fantasy')

# Clue 11
solver.add(child_vars[names.index('Arnold')] == 'Meredith')

# Clue 12
solver.add(name_vars[hair_colors.index('black')] == 'Eric')

# Clue 13
solver.add(book_genre_vars[names.index('Arnold')] == 'science fiction')

# Ensure all values are distinct within their categories
solver.add(Distinct(name_vars))
solver.add(Distinct(house_style_vars))
solver.add(Distinct(hair_color_vars))
solver.add(Distinct(child_vars))
solver.add(Distinct(book_genre_vars))

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": []
        }
    }
    for i in range(4):
        house_number = str(i + 1)
        name = model[name_vars[i]].as_string()[1:-1]
        house_style = model[house_style_vars[i]].as_string()[1:-1]
        hair_color = model[hair_color_vars[i]].as_string()[1:-1]
        child = model[child_vars[i]].as_string()[1:-1]
        book_genre = model[book_genre_vars[i]].as_string()[1:-1]
        solution["solution"]["rows"].append([house_number, name, house_style, hair_color, child, book_genre])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")