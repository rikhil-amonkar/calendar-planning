from z3 import Solver, Int, Distinct, If, Or
import json

# Create a new solver instance
solver = Solver()

# There are 2 houses, so we use index 0 for House 1 and index 1 for House 2.
n = 2

# Create Z3 integer variables for each attribute per house.
# Domain for each variable is 0 or 1.
names = [Int(f"name_{i}") for i in range(n)]
bookGenres = [Int(f"book_{i}") for i in range(n)]
birthdays = [Int(f"birthday_{i}") for i in range(n)]
animals = [Int(f"animal_{i}") for i in range(n)]

# Add domain constraints: each variable can only be 0 or 1.
for var in names + bookGenres + birthdays + animals:
    solver.add(Or(var == 0, var == 1))

# All attributes are unique across houses.
solver.add(Distinct(names))
solver.add(Distinct(bookGenres))
solver.add(Distinct(birthdays))
solver.add(Distinct(animals))

# Define our mapping codes:
# For names: 0 = "Eric", 1 = "Arnold"
# For book genres: 0 = "mystery", 1 = "science fiction"
# For birthdays: 0 = "sept", 1 = "april"
# For animals: 0 = "horse", 1 = "cat"

# Clue 1: Eric is in the first house.
solver.add(names[0] == 0)

# Clue 2: Eric is the person whose birthday is in September.
# Since Eric is in House 1, House 1's birthday is "sept" (coded 0).
solver.add(birthdays[0] == 0)

# Clue 3: The person who loves science fiction books is in the second house.
# So the book genre for House 2 is "science fiction" (coded 1).
solver.add(bookGenres[1] == 1)

# Clue 4: The person who keeps horses is the person whose birthday is in September.
# With our encoding, "horse" is 0 and "sept" is 0.
# Therefore, for each house, if the birthday is sept then the animal must be horse.
# Given there are two houses, an easy way is to require that the animal code equals the birthday code.
for i in range(n):
    solver.add(animals[i] == birthdays[i])

# Solve the constraints
if solver.check() == "sat" or solver.check() == solver.sat:
    model = solver.model()
    
    # Build mapping dictionaries for interpreting the integer codes.
    name_map = {0: "Eric", 1: "Arnold"}
    book_map = {0: "mystery", 1: "science fiction"}
    birthday_map = {0: "sept", 1: "april"}
    animal_map = {0: "horse", 1: "cat"}
    
    rows = []
    # Houses are numbered 1 and 2.
    for i in range(n):
        house_number = str(i + 1)
        name_val = model.evaluate(names[i]).as_long()
        book_val = model.evaluate(bookGenres[i]).as_long()
        birthday_val = model.evaluate(birthdays[i]).as_long()
        animal_val = model.evaluate(animals[i]).as_long()
        
        rows.append([
            house_number,
            name_map[name_val],
            book_map[book_val],
            birthday_map[birthday_val],
            animal_map[animal_val]
        ])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")