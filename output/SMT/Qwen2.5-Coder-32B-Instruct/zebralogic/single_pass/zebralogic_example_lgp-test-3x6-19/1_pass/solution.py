from z3 import *

# Create Solver instance
solver = Solver()

# Define variables
names = ['Arnold', 'Eric', 'Peter']
cigars = ['pall mall', 'blue master', 'prince']
animals = ['horse', 'cat', 'bird']
children = ['Bella', 'Fred', 'Meredith']
book_genres = ['science fiction', 'romance', 'mystery']
phone_models = ['google pixel 6', 'iphone 13', 'samsung galaxy s21']

# Create symbolic variables
house_vars = [Int(f"house_{i}") for i in range(1, 4)]
name_vars = [String(f"name_{i}") for i in range(1, 4)]
cigar_vars = [String(f"cigar_{i}") for i in range(1, 4)]
animal_vars = [String(f"animal_{i}") for i in range(1, 4)]
child_vars = [String(f"child_{i}") for i in range(1, 4)]
book_genre_vars = [String(f"book_genre_{i}") for i in range(1, 4)]
phone_model_vars = [String(f"phone_model_{i}") for i in range(1, 4)]

# Add constraints for unique values in each category
solver.add(Distinct(name_vars))
solver.add(Distinct(cigar_vars))
solver.add(Distinct(animal_vars))
solver.add(Distinct(child_vars))
solver.add(Distinct(book_genre_vars))
solver.add(Distinct(phone_model_vars))

# Add constraints for house numbers
solver.add(Distinct(house_vars))
solver.add(And(house_vars[0] == 1, house_vars[1] == 2, house_vars[2] == 3))

# Clue 1: The person who loves mystery books is the person's child is named Fred.
solver.add(Implies(book_genre_vars[i] == 'mystery', child_vars[i] == 'Fred') for i in range(3))

# Clue 2: The cat lover is Eric.
solver.add(Implies(animal_vars[i] == 'cat', name_vars[i] == 'Eric') for i in range(3))

# Clue 3: The person partial to Pall Mall is in the second house.
solver.add(cigar_vars[1] == 'pall mall')

# Clue 4: The person who keeps horses is the person's child is named Meredith.
solver.add(Implies(animal_vars[i] == 'horse', child_vars[i] == 'Meredith') for i in range(3))

# Clue 5: The person's child is named Bella is the Prince smoker.
solver.add(Implies(child_vars[i] == 'Bella', cigar_vars[i] == 'prince') for i in range(3))

# Clue 6: The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
solver.add(Implies(phone_model_vars[0] == 'iphone 13', phone_model_vars[1] == 'samsung galaxy s21'))
solver.add(Implies(phone_model_vars[1] == 'iphone 13', phone_model_vars[2] == 'samsung galaxy s21'))

# Clue 7: The person's child is named Fred is directly left of Arnold.
solver.add(Implies(child_vars[0] == 'Fred', name_vars[1] == 'Arnold'))
solver.add(Implies(child_vars[1] == 'Fred', name_vars[2] == 'Arnold'))

# Clue 8: Peter is somewhere to the left of Eric.
solver.add(Or(And(name_vars[0] == 'Peter', name_vars[1] == 'Eric'),
             And(name_vars[0] == 'Peter', name_vars[2] == 'Eric'),
             And(name_vars[1] == 'Peter', name_vars[2] == 'Eric')))

# Clue 9: The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
solver.add(Implies(book_genre_vars[i] == 'science fiction', phone_model_vars[i] == 'samsung galaxy s21') for i in range(3))

# Clue 10: The person who loves science fiction books is in the third house.
solver.add(book_genre_vars[2] == 'science fiction')

# Clue 11: The person who loves mystery books is not in the second house.
solver.add(book_genre_vars[1] != 'mystery')

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
            "rows": []
        }
    }
    for i in range(3):
        house = str(i + 1)
        name = model[name_vars[i]].as_string()[1:-1]
        cigar = model[cigar_vars[i]].as_string()[1:-1]
        animal = model[animal_vars[i]].as_string()[1:-1]
        child = model[child_vars[i]].as_string()[1:-1]
        book_genre = model[book_genre_vars[i]].as_string()[1:-1]
        phone_model = model[phone_model_vars[i]].as_string()[1:-1]
        solution["solution"]["rows"].append([house, name, cigar, animal, child, book_genre, phone_model])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")