from z3 import *

# Define variables
house1_name = Int('house1_name')
house2_name = Int('house2_name')
house3_name = Int('house3_name')

house1_smoothie = Int('house1_smoothie')
house2_smoothie = Int('house2_smoothie')
house3_smoothie = Int('house3_smoothie')

house1_book_genre = Int('house1_book_genre')
house2_book_genre = Int('house2_book_genre')
house3_book_genre = Int('house3_book_genre')

# Define domains for each variable
names = [1, 2, 3]  # 1: Eric, 2: Arnold, 3: Peter
smoothies = [1, 2, 3]  # 1: desert, 2: watermelon, 3: cherry
book_genres = [1, 2, 3]  # 1: science fiction, 2: romance, 3: mystery

# Create a solver instance
solver = Solver()

# Add constraints for unique values in each category
solver.add(Distinct(house1_name, house2_name, house3_name))
solver.add(Distinct(house1_smoothie, house2_smoothie, house3_smoothie))
solver.add(Distinct(house1_book_genre, house2_book_genre, house3_book_genre))

# Add domain constraints
solver.add(Or(house1_name == 1, house1_name == 2, house1_name == 3))
solver.add(Or(house2_name == 1, house2_name == 2, house2_name == 3))
solver.add(Or(house3_name == 1, house3_name == 2, house3_name == 3))

solver.add(Or(house1_smoothie == 1, house1_smoothie == 2, house1_smoothie == 3))
solver.add(Or(house2_smoothie == 1, house2_smoothie == 2, house2_smoothie == 3))
solver.add(Or(house3_smoothie == 1, house3_smoothie == 2, house3_smoothie == 3))

solver.add(Or(house1_book_genre == 1, house1_book_genre == 2, house1_book_genre == 3))
solver.add(Or(house2_book_genre == 1, house2_book_genre == 2, house2_book_genre == 3))
solver.add(Or(house3_book_genre == 1, house3_book_genre == 2, house3_book_genre == 3))

# Encode the clues
# Clue 1: The person who likes Cherry smoothies is somewhere to the left of the person who loves mystery books.
# This means if someone likes cherry smoothie in house i, then the person who loves mystery books must be in house i+1 or i+2
solver.add(Or(And(house1_smoothie == 3, Or(house2_book_genre == 3, house3_book_genre == 3)),
              And(house2_smoothie == 3, house3_book_genre == 3)))

# Clue 2: Arnold is the person who loves mystery books.
# Arnold is represented by 2, mystery books by 3
solver.add(Or(house1_name == 2, house2_name == 2, house3_name == 2))
solver.add(Or(house1_book_genre == 3, house2_book_genre == 3, house3_book_genre == 3))
solver.add(Implies(house1_name == 2, house1_book_genre == 3))
solver.add(Implies(house2_name == 2, house2_book_genre == 3))
solver.add(Implies(house3_name == 2, house3_book_genre == 3))

# Clue 3: The person who loves science fiction books is not in the first house.
# Science fiction books are represented by 1
solver.add(Or(house2_book_genre == 1, house3_book_genre == 1))
solver.add(house1_book_genre != 1)

# Clue 4: The Desert smoothie lover is directly left of the person who loves mystery books.
# Desert smoothie is represented by 1, mystery books by 3
solver.add(Or(And(house1_smoothie == 1, house2_book_genre == 3),
              And(house2_smoothie == 1, house3_book_genre == 3)))

# Clue 5: Peter is in the first house.
# Peter is represented by 3
solver.add(house1_name == 3)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": [
                ["1", str(model[house1_name]), str(model[house1_smoothie]), str(model[house1_book_genre])],
                ["2", str(model[house2_name]), str(model[house2_smoothie]), str(model[house2_book_genre])],
                ["3", str(model[house3_name]), str(model[house3_smoothie]), str(model[house3_book_genre])]
            ]
        }
    }
    
    # Map numbers to actual names, smoothies, and book genres
    name_map = {1: "Eric", 2: "Arnold", 3: "Peter"}
    smoothie_map = {1: "desert", 2: "watermelon", 3: "cherry"}
    book_genre_map = {1: "science fiction", 2: "romance", 3: "mystery"}
    
    for row in solution["solution"]["rows"]:
        row[1] = name_map[int(row[1])]
        row[2] = smoothie_map[int(row[2])]
        row[3] = book_genre_map[int(row[3])]
    
    print(solution)
else:
    print("No solution found")