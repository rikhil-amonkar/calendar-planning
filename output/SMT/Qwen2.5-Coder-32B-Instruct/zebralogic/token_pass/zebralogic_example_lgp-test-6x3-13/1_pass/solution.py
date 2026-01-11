from z3 import *

# Define the solver
solver = Solver()

# Define variables
names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
book_genres = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
occupations = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

# Create dictionaries to hold the variables
name_vars = {house: Int(f"name_{house}") for house in range(1, 7)}
book_genre_vars = {house: Int(f"book_genre_{house}") for house in range(1, 7)}
occupation_vars = {house: Int(f"occupation_{house}") for house in range(1, 7)}

# Add constraints for unique values
solver.add(Distinct(name_vars.values()))
solver.add(Distinct(book_genre_vars.values()))
solver.add(Distinct(occupation_vars.values()))

# Map names, book genres, and occupations to integers
name_map = {name: i for i, name in enumerate(names)}
book_genre_map = {genre: i for i, genre in enumerate(book_genres)}
occupation_map = {occupation: i for i, occupation in enumerate(occupations)}

# Add constraints based on the clues
# Clue 1: Alice is the person who loves fantasy books.
solver.add(name_vars[house] == name_map["Alice"] ==>
           book_genre_vars[house] == book_genre_map["fantasy"]) for house in range(1, 7))

# Clue 2: The person who loves mystery books and Bob are next to each other.
for house in range(1, 6):
    solver.add(Or(
        And(book_genre_vars[house] == book_genre_map["mystery"], name_vars[house + 1] == name_map["Bob"]),
        And(book_genre_vars[house + 1] == book_genre_map["mystery"], name_vars[house] == name_map["Bob"])
    ))

# Clue 3: Carol is the person who loves mystery books.
solver.add(name_vars[house] == name_map["Carol"] ==>
           book_genre_vars[house] == book_genre_map["mystery"]) for house in range(1, 7))

# Clue 4: The lawyer is the person who loves fantasy books.
solver.add(occupation_vars[house] == occupation_map["lawyer"] ==>
           book_genre_vars[house] == book_genre_map["fantasy"]) for house in range(1, 7))

# Clue 5: Bob is not in the fifth house.
solver.add(name_vars[5] != name_map["Bob"])

# Clue 6: Arnold is somewhere to the left of the engineer.
for house_arnold in range(1, 6):
    for house_engineer in range(house_arnold + 1, 7):
        solver.add(And(name_vars[house_arnold] == name_map["Arnold"],
                       occupation_vars[house_engineer] == occupation_map["engineer"]))

# Clue 7: The nurse is directly left of Alice.
for house_nurse in range(1, 6):
    solver.add(And(occupation_vars[house_nurse] == occupation_map["nurse"],
                   name_vars[house_nurse + 1] == name_map["Alice"]))

# Clue 8: The teacher loves biography books.
solver.add(occupation_vars[house] == occupation_map["teacher"] ==>
           book_genre_vars[house] == book_genre_map["biography"]) for house in range(1, 7))

# Clue 9: The person who loves historical fiction is somewhere to the left of the teacher.
for house_historical in range(1, 6):
    for house_teacher in range(house_historical + 1, 7):
        solver.add(And(book_genre_vars[house_historical] == book_genre_map["historical fiction"],
                       occupation_vars[house_teacher] == occupation_map["teacher"]))

# Clue 10: The doctor is in the first house.
solver.add(occupation_vars[1] == occupation_map["doctor"])

# Clue 11: The artist loves science fiction books.
solver.add(occupation_vars[house] == occupation_map["artist"] ==>
           book_genre_vars[house] == book_genre_map["science fiction"]) for house in range(1, 7))

# Clue 12: Eric is in the third house.
solver.add(name_vars[3] == name_map["Eric"])

# Clue 13: The person who loves mystery books is not in the fifth house.
solver.add(book_genre_vars[5] != book_genre_map["mystery"])

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in range(1, 7):
        name = names[model.evaluate(name_vars[house]).as_long()]
        book_genre = book_genres[model.evaluate(book_genre_vars[house]).as_long()]
        occupation = occupations[model.evaluate(occupation_vars[house]).as_long()]
        solution.append([str(house), name, book_genre, occupation])
    
    # Print the solution in JSON format
    print({
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": solution
        }
    })
else:
    print("No solution found")