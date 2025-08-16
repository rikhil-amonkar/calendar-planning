from z3 import *

# Create variables for each attribute
names = ['Arnold', 'Eric', 'Peter']
music_genres = ['pop', 'rock', 'classical']
children = ['Fred', 'Meredith', 'Bella']
book_genres = ['mystery', 'romance', 'science fiction']

# Create symbolic variables
house_names = [String('name_%d' % i) for i in range(3)]
house_music_genres = [String('music_genre_%d' % i) for i in range(3)]
house_children = [String('child_%d' % i) for i in range(3)]
house_book_genres = [String('book_genre_%d' % i) for i in range(3)]

# Create a solver instance
solver = Solver()

# Add constraints for unique values within each category
solver.add(Distinct(house_names))
solver.add(Distinct(house_music_genres))
solver.add(Distinct(house_children))
solver.add(Distinct(house_book_genres))

# Add constraints based on clues
# Clue 2: Peter is in the first house.
solver.add(house_names[0] == 'Peter')

# Clue 5: Eric is the person who loves mystery books.
for i in range(3):
    solver.add(Implies(house_names[i] == 'Eric', house_book_genres[i] == 'mystery'))
    solver.add(Implies(house_book_genres[i] == 'mystery', house_names[i] == 'Eric'))

# Clue 3: The person who loves mystery books is the person who loves classical music.
for i in range(3):
    solver.add(Implies(house_book_genres[i] == 'mystery', house_music_genres[i] == 'classical'))

# Clue 4: The person who loves science fiction books is the person's child is named Meredith.
for i in range(3):
    solver.add(Implies(house_book_genres[i] == 'science fiction', house_children[i] == 'Meredith'))

# Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
for i in range(3):
    for j in range(3):
        if i < j:
            solver.add(Implies(house_music_genres[j] == 'rock', house_music_genres[i] == 'romance'))

# Clue 1: The person's child is named Fred is directly left of the person who loves mystery books.
for i in range(2):  # Only need to check up to index 1 because Fred must be left of someone
    solver.add(Implies(house_children[i] == 'Fred', house_book_genres[i+1] == 'mystery'))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": []
        }
    }
    for i in range(3):
        name = model[house_names[i]].as_string()[1:-1]
        music_genre = model[house_music_genres[i]].as_string()[1:-1]
        child = model[house_children[i]].as_string()[1:-1]
        book_genre = model[house_book_genres[i]].as_string()[1:-1]
        solution["solution"]["rows"].append([str(i+1), name, music_genre, child, book_genre])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")