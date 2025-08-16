from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define the attributes
names = ["Arnold", "Eric", "Peter"]
music_genres = ["pop", "rock", "classical"]
children = ["Fred", "Meredith", "Bella"]
book_genres = ["mystery", "romance", "science fiction"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
music = {h: String(f"music_{h}") for h in houses}
child = {h: String(f"child_{h}") for h in houses}
book = {h: String(f"book_{h}") for h in houses}

# Add constraints that each attribute is one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([music[h] == m for m in music_genres]))
    s.add(Or([child[h] == c for c in children]))
    s.add(Or([book[h] == b for b in book_genres]))

# Add constraints that all attributes are unique within their category
for h1 in houses:
    for h2 in houses:
        if h1 < h2:
            s.add(name[h1] != name[h2])
            s.add(music[h1] != music[h2])
            s.add(child[h1] != child[h2])
            s.add(book[h1] != book[h2])

# Clue 2: Peter is in the first house.
s.add(name[1] == "Peter")

# Clue 5: Eric is the person who loves mystery books.
# So Eric's book genre is mystery, and his name is Eric.
for h in houses:
    s.add(Implies(book[h] == "mystery", name[h] == "Eric"))

# Clue 3: The person who loves mystery books is the person who loves classical music.
for h in houses:
    s.add(Implies(book[h] == "mystery", music[h] == "classical"))

# Clue 1: The person whose child is named Fred is directly left of the person who loves mystery books.
# This means the house with child Fred is immediately to the left of the house with book mystery.
s.add(Or(
    And(child[1] == "Fred", book[2] == "mystery"),
    And(child[2] == "Fred", book[3] == "mystery")
))

# Clue 4: The person who loves science fiction books is the person whose child is named Meredith.
for h in houses:
    s.add(Implies(book[h] == "science fiction", child[h] == "Meredith"))

# Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
# This means the house with rock music has a higher number than the house with romance books.
for h_romance in houses:
    for h_rock in houses:
        if h_rock > h_romance:
            s.add(Implies(And(book[h_romance] == "romance", music[h_rock] == "rock"), h_rock > h_romance))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": []
        }
    }
    for h in sorted(houses):
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(music[h]).as_string(),
            model.eval(child[h]).as_string(),
            model.eval(book[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")