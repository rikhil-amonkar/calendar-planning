from z3 import *

# Create a solver instance
solver = Solver()

# Define domains
houses = [1, 2, 3, 4]
names = ["Arnold", "Peter", "Eric", "Alice"]
house_styles = ["craftsman", "colonial", "victorian", "ranch"]
hair_colors = ["red", "blonde", "black", "brown"]
children = ["Bella", "Fred", "Meredith", "Samantha"]
book_genres = ["mystery", "fantasy", "romance", "science fiction"]

# Create variables
name_vars = {house: Int(f"name_{house}") for house in houses}
house_style_vars = {house: Int(f"house_style_{house}") for house in houses}
hair_color_vars = {house: Int(f"hair_color_{house}") for house in houses}
child_vars = {house: Int(f"child_{house}") for house in houses}
book_genre_vars = {house: Int(f"book_genre_{house}") for house in houses}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([house_style_vars[house] for house in houses]))
solver.add(Distinct([hair_color_vars[house] for house in houses]))
solver.add(Distinct([child_vars[house] for house in houses]))
solver.add(Distinct([book_genre_vars[house] for house in houses]))

# Map strings to integer values
name_map = {name: i for i, name in enumerate(names)}
house_style_map = {style: i for i, style in enumerate(house_styles)}
hair_color_map = {color: i for i, color in enumerate(hair_colors)}
child_map = {child: i for i, child in enumerate(children)}
book_genre_map = {genre: i for i, genre in enumerate(book_genres)}

# Add specific constraints
solver.add(house_style_vars[3] == house_style_map["craftsman"])
solver.add(name_vars[i] == name_map["Alice"] for i in houses if book_genre_vars[i] == book_genre_map["romance"])
solver.add(hair_color_vars[4] == hair_color_map["brown"])
solver.add(child_vars[4] == child_map["Samantha"])
solver.add(Or([And(house_style_vars[i] == house_style_map["ranch"], hair_color_vars[j] != hair_color_map["red"]) for i in range(2, 5) for j in range(1, i)]))
solver.add(name_vars[i] == name_map["Peter"] for i in houses if child_vars[i] == child_map["Bella"])
solver.add(hair_color_vars[i] == hair_color_map["red"] for i in houses if name_vars[i] == name_map["Arnold"])
solver.add(name_vars[i] == name_map["Alice"] for i in houses if house_style_vars[i] == house_style_map["colonial"])
solver.add(hair_color_vars[2] == hair_color_map["black"])
solver.add(name_vars[i] == name_map["Peter"] for i in houses if book_genre_vars[i] == book_genre_map["fantasy"])
solver.add(name_vars[i] == name_map["Arnold"] for i in houses if child_vars[i] == child_map["Meredith"])
solver.add(name_vars[i] == name_map["Eric"] for i in houses if hair_color_vars[i] == hair_color_map["black"])
solver.add(name_vars[i] == name_map["Arnold"] for i in houses if book_genre_vars[i] == book_genre_map["science fiction"])

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        house_style = house_styles[model.evaluate(house_style_vars[house]).as_long()]
        hair_color = hair_colors[model.evaluate(hair_color_vars[house]).as_long()]
        child = children[model.evaluate(child_vars[house]).as_long()]
        book_genre = book_genres[model.evaluate(book_genre_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, house_style, hair_color, child, book_genre])
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")