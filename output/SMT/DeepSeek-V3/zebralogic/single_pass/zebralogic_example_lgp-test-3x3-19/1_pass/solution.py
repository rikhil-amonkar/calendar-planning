import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define the attributes
names = ["Eric", "Arnold", "Peter"]
smoothies = ["desert", "watermelon", "cherry"]
book_genres = ["science fiction", "romance", "mystery"]

# Create variables for each attribute in each house
name_vars = {house: String(f"name_{house}") for house in houses}
smoothie_vars = {house: String(f"smoothie_{house}") for house in houses}
book_genre_vars = {house: String(f"book_genre_{house}") for house in houses}

# Add constraints that each attribute must be one of the allowed values
for house in houses:
    s.add(Or([name_vars[house] == name for name in names]))
    s.add(Or([smoothie_vars[house] == smoothie for smoothie in smoothies]))
    s.add(Or([book_genre_vars[house] == genre for genre in book_genres]))

# Add constraints that all attributes in each category are distinct
s.add(Distinct([name_vars[house] for house in houses]))
s.add(Distinct([smoothie_vars[house] for house in houses]))
s.add(Distinct([book_genre_vars[house] for house in houses]))

# Clue 5: Peter is in the first house.
s.add(name_vars[1] == "Peter")

# Clue 2: Arnold is the person who loves mystery books.
# So Arnold's book genre is mystery, and no one else has mystery.
for house in houses:
    s.add(Implies(name_vars[house] == "Arnold", book_genre_vars[house] == "mystery"))
    s.add(Implies(book_genre_vars[house] == "mystery", name_vars[house] == "Arnold"))

# Clue 3: The person who loves science fiction books is not in the first house.
s.add(Or(book_genre_vars[2] == "science fiction", book_genre_vars[3] == "science fiction"))

# Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
# This means the desert smoothie is in house X, and mystery books are in house X+1.
for house in [1, 2]:
    s.add(Implies(smoothie_vars[house] == "desert", book_genre_vars[house + 1] == "mystery"))
    s.add(Implies(book_genre_vars[house + 1] == "mystery", smoothie_vars[house] == "desert"))

# Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
# So cherry is in house X, and mystery is in house Y where X < Y.
# We need to ensure that if cherry is in house X, then mystery is in some house Y > X.
# This can be modeled by ensuring that if cherry is in house 1, mystery is in 2 or 3; if cherry is in 2, mystery is in 3.
s.add(Or(
    And(smoothie_vars[1] == "cherry", Or(book_genre_vars[2] == "mystery", book_genre_vars[3] == "mystery")),
    And(smoothie_vars[2] == "cherry", book_genre_vars[3] == "mystery"),
    smoothie_vars[3] != "cherry"  # cherry cannot be in house 3 because no house is to its right
))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": []
        }
    }
    for house in houses:
        name = model.eval(name_vars[house]).as_string()
        smoothie = model.eval(smoothie_vars[house]).as_string()
        book_genre = model.eval(book_genre_vars[house]).as_string()
        solution["solution"]["rows"].append([str(house), name, smoothie, book_genre])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")