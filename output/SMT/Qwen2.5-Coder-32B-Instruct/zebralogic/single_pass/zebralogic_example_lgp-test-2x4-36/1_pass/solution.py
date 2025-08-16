from z3 import *

# Create Solver instance
solver = Solver()

# Define variables for each attribute for both houses
name_house1, name_house2 = Ints('name_house1 name_house2')
book_genre_house1, book_genre_house2 = Ints('book_genre_house1 book_genre_house2')
birthday_house1, birthday_house2 = Ints('birthday_house1 birthday_house2')
animal_house1, animal_house2 = Ints('animal_house1 animal_house2')

# Define domains for each variable
names = {'Eric': 1, 'Arnold': 2}
book_genres = {'science fiction': 1, 'mystery': 2}
birthdays = {'april': 1, 'sept': 2}
animals = {'horse': 1, 'cat': 2}

# Constraints based on clues
# Clue 1: Eric is in the first house.
solver.add(name_house1 == names['Eric'])

# Clue 2: Eric is the person whose birthday is in September.
solver.add(birthday_house1 == birthdays['sept'])

# Clue 3: The person who loves science fiction books is in the second house.
solver.add(book_genre_house2 == book_genres['science fiction'])

# Clue 4: The person who keeps horses is the person whose birthday is in September.
solver.add(animal_house1 == animals['horse'])

# Different people in each house
solver.add(name_house1 != name_house2)

# Different book genres in each house
solver.add(book_genre_house1 != book_genre_house2)

# Different birthdays in each house
solver.add(birthday_house1 != birthday_house2)

# Different animals in each house
solver.add(animal_house1 != animal_house2)

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    
    # Extract the solution
    solution_house1 = [
        "1",
        [k for k, v in names.items() if v == model[name_house1].as_long()][0],
        [k for k, v in book_genres.items() if v == model[book_genre_house1].as_long()][0],
        [k for k, v in birthdays.items() if v == model[birthday_house1].as_long()][0],
        [k for k, v in animals.items() if v == model[animal_house1].as_long()][0]
    ]
    
    solution_house2 = [
        "2",
        [k for k, v in names.items() if v == model[name_house2].as_long()][0],
        [k for k, v in book_genres.items() if v == model[book_genre_house2].as_long()][0],
        [k for k, v in birthdays.items() if v == model[birthday_house2].as_long()][0],
        [k for k, v in animals.items() if v == model[animal_house2].as_long()][0]
    ]
    
    # Prepare the final output in JSON format
    final_solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": [solution_house1, solution_house2]
        }
    }
    
    print(final_solution)
else:
    print("No solution found")