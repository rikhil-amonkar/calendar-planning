from z3 import *

# Define the domains for each variable
houses = [1, 2, 3, 4]
names = ["Arnold", "Peter", "Eric", "Alice"]
house_styles = ["craftsman", "colonial", "victorian", "ranch"]
hair_colors = ["red", "blonde", "black", "brown"]
children = ["Bella", "Fred", "Meredith", "Samantha"]
book_genres = ["mystery", "fantasy", "romance", "science fiction"]

# Create variables for each attribute in each house
name_vars = {house: Int(f"name_{house}") for house in houses}
house_style_vars = {house: Int(f"house_style_{house}") for house in houses}
hair_color_vars = {house: Int(f"hair_color_{house}") for house in houses}
child_vars = {house: Int(f"child_{house}") for house in houses}
book_genre_vars = {house: Int(f"book_genre_{house}") for house in houses}

# Create a solver instance
solver = Solver()

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([house_style_vars[house] for house in houses]))
solver.add(Distinct([hair_color_vars[house] for house in houses]))
solver.add(Distinct([child_vars[house] for house in houses]))
solver.add(Distinct([book_genre_vars[house] for house in houses]))

# Translate clues into constraints
# Clue 1: The person in a Craftsman-style house is in the third house.
solver.add(house_style_vars[3] == house_styles.index("craftsman"))

# Clue 2: Alice is the person who loves romance books.
solver.add(name_vars[houses.index(next(house for house, genre in book_genre_vars.items() if genre == book_genres.index("romance")))] == names.index("Alice"))

# Clue 3: The person who has brown hair is in the fourth house.
solver.add(hair_color_vars[4] == hair_colors.index("brown"))

# Clue 4: The person's child is named Samantha is in the fourth house.
solver.add(child_vars[4] == children.index("Samantha"))

# Clue 5: The person in a ranch-style home is somewhere to the right of the person who has red hair.
red_hair_house = Int('red_hair_house')
solver.add(Or([And(hair_color_vars[house] == hair_colors.index("red"), red_hair_house == house) for house in houses]))
solver.add(Or([And(house_style_vars[house] == house_styles.index("ranch"), house > red_hair_house) for house in houses]))

# Clue 6: Peter is the person's child is named Bella.
solver.add(name_vars[houses.index(next(house for house, child in child_vars.items() if child == children.index("Bella")))] == names.index("Peter"))

# Clue 7: Arnold is the person who has red hair.
solver.add(name_vars[houses.index(next(house for house, color in hair_color_vars.items() if color == hair_colors.index("red")))] == names.index("Arnold"))

# Clue 8: Alice is the person living in a colonial-style house.
solver.add(name_vars[houses.index(next(house for house, style in house_style_vars.items() if style == house_styles.index("colonial")))] == names.index("Alice"))

# Clue 9: The person who has black hair is in the second house.
solver.add(hair_color_vars[2] == hair_colors.index("black"))

# Clue 10: The person who loves fantasy books is Peter.
solver.add(book_genre_vars[houses.index(next(house for house, name in name_vars.items() if name == names.index("Peter")))] == book_genres.index("fantasy"))

# Clue 11: Arnold is the person's child is named Meredith.
solver.add(name_vars[houses.index(next(house for house, child in child_vars.items() if child == children.index("Meredith")))] == names.index("Arnold"))

# Clue 12: The person who has black hair is Eric.
solver.add(name_vars[houses.index(next(house for house, color in hair_color_vars.items() if color == hair_colors.index("black")))] == names.index("Eric"))

# Clue 13: The person who loves science fiction books is Arnold.
solver.add(book_genre_vars[houses.index(next(house for house, name in name_vars.items() if name == names.index("Arnold")))] == book_genres.index("science fiction"))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        house_style = house_styles[model[house_style_vars[house]].as_long()]
        hair_color = hair_colors[model[hair_color_vars[house]].as_long()]
        child = children[model[child_vars[house]].as_long()]
        book_genre = book_genres[model[book_genre_vars[house]].as_long()]
        solution["solution"]["rows"].append([str(house), name, house_style, hair_color, child, book_genre])
    
    print(solution)
else:
    print("No solution found")