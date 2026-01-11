from z3 import *

# Define variables for each attribute for each house
names = [Int(f"name_{i}") for i in range(1, 4)]
cigars = [Int(f"cigar_{i}") for i in range(1, 4)]
animals = [Int(f"animal_{i}") for i in range(1, 4)]
children = [Int(f"child_{i}") for i in range(1, 4)]
book_genres = [Int(f"book_genre_{i}") for i in range(1, 4)]
phone_models = [Int(f"phone_model_{i}") for i in range(1, 4)]

# Define domains for each variable
names_domain = {1: "Arnold", 2: "Eric", 3: "Peter"}
cigars_domain = {1: "pall mall", 2: "blue master", 3: "prince"}
animals_domain = {1: "horse", 2: "cat", 3: "bird"}
children_domain = {1: "Bella", 2: "Fred", 3: "Meredith"}
book_genres_domain = {1: "science fiction", 2: "romance", 3: "mystery"}
phone_models_domain = {1: "google pixel 6", 2: "iphone 13", 3: "samsung galaxy s21"}

# Create a solver instance
solver = Solver()

# Add constraints for uniqueness
solver.add(Distinct(names))
solver.add(Distinct(cigars))
solver.add(Distinct(animals))
solver.add(Distinct(children))
solver.add(Distinct(book_genres))
solver.add(Distinct(phone_models))

# Add constraints based on the clues
# Clue 1
solver.add(Implies(book_genres[0] == 3, children[0] == 2))  # mystery -> Fred

# Clue 2
solver.add(Implies(animals[1] == 2, names[1] == 2))  # cat -> Eric

# Clue 3
solver.add(cigars[1] == 1)  # Pall Mall -> house 2

# Clue 4
solver.add(Implies(animals[0] == 1, children[0] == 3))  # horse -> Meredith

# Clue 5
solver.add(Implies(children[2] == 1, cigars[2] == 3))  # Bella -> prince

# Clue 6
solver.add(Implies(phone_models[0] == 2, phone_models[1] == 3))  # iPhone 13 -> left of Samsung Galaxy S21

# Clue 7
solver.add(Implies(children[0] == 2, names[1] == 1))  # Fred -> left of Arnold

# Clue 8
solver.add(names[0] != 3)  # Peter cannot be in house 1 if Eric is to his right
solver.add(names[1] != 3)  # Peter cannot be in house 2 if Eric is to his right

# Clue 9
solver.add(Implies(book_genres[2] == 1, phone_models[2] == 3))  # science fiction -> Samsung Galaxy S21

# Clue 10
solver.add(book_genres[2] == 1)  # science fiction -> house 3

# Clue 11
solver.add(book_genres[1] != 3)  # mystery not in house 2

# Solve the system
if solver.check() == sat:
    m = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
            "rows": []
        }
    }
    for i in range(3):
        house = i + 1
        name = names_domain[m.eval(names[i]).as_long()]
        cigar = cigars_domain[m.eval(cigars[i]).as_long()]
        animal = animals_domain[m.eval(animals[i]).as_long()]
        child = children_domain[m.eval(children[i]).as_long()]
        book_genre = book_genres_domain[m.eval(book_genres[i]).as_long()]
        phone_model = phone_models_domain[m.eval(phone_models[i]).as_long()]
        solution["solution"]["rows"].append([str(house), name, cigar, animal, child, book_genre, phone_model])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")