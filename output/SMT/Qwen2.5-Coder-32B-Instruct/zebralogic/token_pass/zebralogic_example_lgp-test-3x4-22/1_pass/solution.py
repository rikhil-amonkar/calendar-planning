from z3 import *

# Define the domain for each attribute
names = ['Arnold', 'Eric', 'Peter']
music_genres = ['pop', 'rock', 'classical']
children = ['Fred', 'Meredith', 'Bella']
book_genres = ['mystery', 'romance', 'science fiction']

# Create variables for each attribute for each house
house_names = [String('name_%d' % i) for i in range(3)]
house_music_genres = [String('music_genre_%d' % i) for i in range(3)]
house_children = [String('child_%d' % i) for i in range(3)]
house_book_genres = [String('book_genre_%d' % i) for i in range(3)]

# Create a solver instance
solver = Solver()

# Add constraints for each house to have a unique value for each attribute
for house in range(3):
    solver.add(house_names[house] == Or(*[name for name in names]))
    solver.add(house_music_genres[house] == Or(*[genre for genre in music_genres]))
    solver.add(house_children[house] == Or(*[child for child in children]))
    solver.add(house_book_genres[house] == Or(*[genre for genre in book_genres]))

# Ensure all attributes are unique across houses
solver.add(Distinct(house_names))
solver.add(Distinct(house_music_genres))
solver.add(Distinct(house_children))
solver.add(Distinct(house_book_genres))

# Add specific constraints based on the clues
# Clue 2: Peter is in the first house
solver.add(house_names[0] == 'Peter')

# Clue 5: Eric is the person who loves mystery books
solver.add(house_names[i] == 'Eric' for i in range(3) if house_book_genres[i] == 'mystery')

# Clue 3: The person who loves mystery books is the person who loves classical music
solver.add(Or([And(house_book_genres[i] == 'mystery', house_music_genres[i] == 'classical') for i in range(3)]))

# Clue 4: The person who loves science fiction books is the person's child named Meredith
solver.add(Or([And(house_book_genres[i] == 'science fiction', house_children[i] == 'Meredith') for i in range(3)]))

# Clue 1: The person's child is named Fred is directly left of the person who loves mystery books
solver.add(Or([And(house_children[i] == 'Fred', house_book_genres[i+1] == 'mystery') for i in range(2)]))

# Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books
solver.add(Or([And(house_music_genres[i] == 'romance', house_music_genres[j] == 'rock') for i in range(3) for j in range(i+1, 3)]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in range(3):
        name = model[house_names[house]].as_string()[1:-1]
        music_genre = model[house_music_genres[house]].as_string()[1:-1]
        child = model[house_children[house]].as_string()[1:-1]
        book_genre = model[house_book_genres[house]].as_string()[1:-1]
        solution.append([str(house + 1), name, music_genre, child, book_genre])
    
    result = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": solution
        }
    }
    print(result)
else:
    print("No solution found")