from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2]

# Define the attributes and their possible values
names = ["Arnold", "Eric"]
book_genres = ["science fiction", "mystery"]
vacations = ["mountain", "beach"]
animals = ["cat", "horse"]
music_genres = ["rock", "pop"]

# Create dictionaries to hold the variables for each attribute per house
name = {h: String(f"name_{h}") for h in houses}
book_genre = {h: String(f"book_genre_{h}") for h in houses}
vacation = {h: String(f"vacation_{h}") for h in houses}
animal = {h: String(f"animal_{h}") for h in houses}
music_genre = {h: String(f"music_genre_{h}") for h in houses}

# Add constraints that each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([book_genre[h] == bg for bg in book_genres]))
    s.add(Or([vacation[h] == v for v in vacations]))
    s.add(Or([animal[h] == a for a in animals]))
    s.add(Or([music_genre[h] == mg for mg in music_genres]))

# Add uniqueness constraints for each attribute across houses
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([book_genre[h] for h in houses]))
s.add(Distinct([vacation[h] for h in houses]))
s.add(Distinct([animal[h] for h in houses]))
s.add(Distinct([music_genre[h] for h in houses]))

# Clue 1: The person who loves beach vacations is Eric.
for h in houses:
    s.add(Implies(vacation[h] == "beach", name[h] == "Eric"))

# Clue 2: The person who loves pop music is the person who loves beach vacations.
for h in houses:
    s.add(Implies(music_genre[h] == "pop", vacation[h] == "beach"))
    s.add(Implies(vacation[h] == "beach", music_genre[h] == "pop"))

# Clue 3: The person who loves rock music is the person who loves mystery books.
for h in houses:
    s.add(Implies(music_genre[h] == "rock", book_genre[h] == "mystery"))
    s.add(Implies(book_genre[h] == "mystery", music_genre[h] == "rock"))

# Clue 4: The cat lover is not in the second house.
s.add(animal[1] == "cat")

# Clue 5: The person who loves mystery books is in the first house.
s.add(book_genre[1] == "mystery")

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": []
        }
    }
    for h in sorted(houses):
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(book_genre[h]).as_string(),
            model.eval(vacation[h]).as_string(),
            model.eval(animal[h]).as_string(),
            model.eval(music_genre[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")