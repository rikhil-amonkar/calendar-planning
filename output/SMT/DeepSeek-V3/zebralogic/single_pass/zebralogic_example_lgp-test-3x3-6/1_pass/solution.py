from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define the attributes
names = ["Eric", "Arnold", "Peter"]
book_genres = ["mystery", "science fiction", "romance"]
vacations = ["mountain", "beach", "city"]

# Create variables for each attribute in each house
name_vars = {house: String(f"name_{house}") for house in houses}
book_genre_vars = {house: String(f"book_genre_{house}") for house in houses}
vacation_vars = {house: String(f"vacation_{house}") for house in houses}

# Add constraints that each attribute is one of the allowed values
for house in houses:
    s.add(Or([name_vars[house] == name for name in names]))
    s.add(Or([book_genre_vars[house] == genre for genre in book_genres]))
    s.add(Or([vacation_vars[house] == vacation for vacation in vacations]))

# Add constraints that all attributes are unique
s.add(Distinct([name_vars[house] for house in houses]))
s.add(Distinct([book_genre_vars[house] for house in houses]))
s.add(Distinct([vacation_vars[house] for house in houses]))

# Clue 1: Eric is directly left of Arnold.
s.add(Or(
    And(name_vars[1] == "Eric", name_vars[2] == "Arnold"),
    And(name_vars[2] == "Eric", name_vars[3] == "Arnold")
))

# Clue 2: Peter is somewhere to the right of the person who loves beach vacations.
# This means beach vacation is to the left of Peter.
s.add(Exists([house for house in houses],
    And(
        vacation_vars[house] == "beach",
        ForAll([other_house for other_house in houses if other_house > house],
            name_vars[other_house] != "Peter"
        )
    )
))

# Clue 3: Peter is the person who prefers city breaks.
s.add(ForAll([house for house in houses],
    Implies(name_vars[house] == "Peter", vacation_vars[house] == "city")
))

# Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
# This means mystery is to the left of beach.
s.add(Exists([house_mystery, house_beach],
    And(
        house_mystery < house_beach,
        book_genre_vars[house_mystery] == "mystery",
        vacation_vars[house_beach] == "beach"
    )
))

# Clue 5: The person who loves science fiction books is the person who loves beach vacations.
s.add(ForAll([house for house in houses],
    Implies(vacation_vars[house] == "beach", book_genre_vars[house] == "science fiction")
))

# Solve the problem
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation"],
            "rows": []
        }
    }
    for house in sorted(houses):
        name = model.eval(name_vars[house])
        book_genre = model.eval(book_genre_vars[house])
        vacation = model.eval(vacation_vars[house])
        solution["solution"]["rows"].append([str(house), str(name), str(book_genre), str(vacation)])
    print(solution)
else:
    print("No solution found")