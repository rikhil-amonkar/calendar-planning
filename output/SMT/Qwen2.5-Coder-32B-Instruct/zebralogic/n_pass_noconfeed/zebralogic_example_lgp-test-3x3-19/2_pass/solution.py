from z3 import *

# Create a solver instance
solver = Solver()

# Define the domains
houses = [1, 2, 3]
names = ["Eric", "Arnold", "Peter"]
smoothies = ["desert", "watermelon", "cherry"]
book_genres = ["science fiction", "romance", "mystery"]

# Create dictionaries to map each attribute to a variable
name_vars = {house: Int(f"name_{house}") for house in houses}
smoothie_vars = {house: Int(f"smoothie_{house}") for house in houses}
book_genre_vars = {house: Int(f"book_genre_{house}") for house in houses}

# Add constraints for unique values in each category
solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([smoothie_vars[house] for house in houses]))
solver.add(Distinct([book_genre_vars[house] for house in houses]))

# Map names, smoothies, and book genres to integers
name_map = {name: i for i, name in enumerate(names)}
smoothie_map = {smoothie: i for i, smoothie in enumerate(smoothies)}
book_genre_map = {genre: i for i, genre in enumerate(book_genres)}

# Add constraints based on the clues
# Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
solver.add(Or(smoothie_vars[house] != smoothie_map["cherry"], book_genre_vars[house + 1] == book_genre_map["mystery"]) for house in houses if house < 3)

# Clue 2: Arnold is the person who loves mystery books.
solver.add(Implies(name_vars[house] == name_map["Arnold"], book_genre_vars[house] == book_genre_map["mystery"]) for house in houses)

# Clue 3: The person who loves science fiction books is not in the first house.
solver.add(book_genre_vars[1] != book_genre_map["science fiction"])

# Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
solver.add(Implies(smoothie_vars[house] == smoothie_map["desert"], book_genre_vars[house + 1] == book_genre_map["mystery"]) for house in houses if house < 3)

# Clue 5: Peter is in the first house.
solver.add(name_vars[1] == name_map["Peter"])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": []
        }
    }
    
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        smoothie = smoothies[model.evaluate(smoothie_vars[house]).as_long()]
        book_genre = book_genres[model.evaluate(book_genre_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, smoothie, book_genre])
    
    import json
    print(json.dumps(solution))
else:
    print("No solution found")