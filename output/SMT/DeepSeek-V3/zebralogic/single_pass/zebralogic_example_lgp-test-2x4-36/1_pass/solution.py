from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2]

# Define the attributes
names = ["Eric", "Arnold"]
book_genres = ["science fiction", "mystery"]
birthday_months = ["april", "sept"]
animals = ["horse", "cat"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
book_genre = {h: String(f"book_genre_{h}") for h in houses}
birthday = {h: String(f"birthday_{h}") for h in houses}
animal = {h: String(f"animal_{h}") for h in houses}

# Add constraints for uniqueness
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([book_genre[h] for h in houses]))
s.add(Distinct([birthday[h] for h in houses]))
s.add(Distinct([animal[h] for h in houses]))

# Each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([book_genre[h] == bg for bg in book_genres]))
    s.add(Or([birthday[h] == bm for bm in birthday_months]))
    s.add(Or([animal[h] == a for a in animals]))

# Apply the given clues
# Clue 1: Eric is in the first house.
s.add(name[1] == "Eric")

# Clue 2: Eric is the person whose birthday is in September.
s.add(birthday[1] == "sept")

# Clue 3: The person who loves science fiction books is in the second house.
s.add(book_genre[2] == "science fiction")

# Clue 4: The person who keeps horses is the person whose birthday is in September.
# Since Eric's birthday is in September, he keeps the horse.
s.add(animal[1] == "horse")

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": []
        }
    }
    
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(book_genre[h]).as_string(),
            model.eval(birthday[h]).as_string(),
            model.eval(animal[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    
    # Convert to JSON
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")