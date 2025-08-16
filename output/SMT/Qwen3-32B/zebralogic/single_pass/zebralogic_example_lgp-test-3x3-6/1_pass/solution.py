import z3
import json

# Define EnumSorts
Names, (Eric, Arnold, Peter) = z3.EnumSort('Names', ['Eric', 'Arnold', 'Peter'])
BookGenres, (Mystery, SciFi, Romance) = z3.EnumSort('BookGenres', ['Mystery', 'SciFi', 'Romance'])
Vacations, (Mountain, Beach, City) = z3.EnumSort('Vacations', ['Mountain', 'Beach', 'City'])

# Create variables for each house (1, 2, 3)
names = [z3.Const(f'name_{i}', Names) for i in [1, 2, 3]]
books = [z3.Const(f'book_{i}', BookGenres) for i in [1, 2, 3]]
vacations = [z3.Const(f'vacation_{i}', Vacations) for i in [1, 2, 3]]

s = z3.Solver()

# Add distinctness constraints
s.add(z3.Distinct(names))
s.add(z3.Distinct(books))
s.add(z3.Distinct(vacations))

# Clue 1: Eric directly left of Arnold
s.add(z3.Or(
    z3.And(names[0] == Eric, names[1] == Arnold),
    z3.And(names[1] == Eric, names[2] == Arnold)
))

# Create integer variables for house positions
beach_house = z3.Int('beach_house')
peter_house = z3.Int('peter_house')
mystery_house = z3.Int('mystery_house')

# Add constraints linking these variables to the attributes
for i in range(3):
    # For house i+1 (since i is 0,1,2)
    s.add(z3.Implies(vacations[i] == Beach, beach_house == (i + 1)))
    s.add(z3.Implies(names[i] == Peter, peter_house == (i + 1)))
    s.add(z3.Implies(books[i] == Mystery, mystery_house == (i + 1)))

# Clue 2: Peter is to the right of beach
s.add(peter_house > beach_house)

# Clue 3: Peter's vacation is city
for i in range(3):
    s.add(z3.Implies(names[i] == Peter, vacations[i] == City))

# Clue 4: mystery is left of beach
s.add(mystery_house < beach_house)

# Clue 5: SciFi implies Beach
for i in range(3):
    s.add(z3.Implies(books[i] == SciFi, vacations[i] == Beach))

if s.check() == z3.sat:
    model = s.model()
    # Extract the solution
    solution = []
    for i in range(3):
        house_num = str(i + 1)
        name = model.eval(names[i]).decl().name()
        book = model.eval(books[i]).decl().name()
        vacation = model.eval(vacations[i]).decl().name()
        solution.append([house_num, name, book, vacation])
    # Format as JSON
    json_output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation"],
            "rows": solution
        }
    }
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")