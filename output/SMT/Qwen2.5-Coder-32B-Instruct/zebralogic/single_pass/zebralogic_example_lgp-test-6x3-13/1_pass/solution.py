from z3 import *

# Create a solver instance
solver = Solver()

# Define variables for each house
names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
book_genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']

# Create dictionaries to hold the variables
house_vars = {}
for i in range(1, 7):
    house_vars[i] = {
        'name': Int(f'name_{i}'),
        'book_genre': Int(f'book_genre_{i}'),
        'occupation': Int(f'occupation_{i}')
    }

# Add constraints for unique values in each category
solver.add(Distinct([house_vars[i]['name'] for i in range(1, 7)]))
solver.add(Distinct([house_vars[i]['book_genre'] for i in range(1, 7)]))
solver.add(Distinct([house_vars[i]['occupation'] for i in range(1, 7)]))

# Map names, book genres, and occupations to integers
name_map = {name: i for i, name in enumerate(names)}
book_genre_map = {genre: i for i, genre in enumerate(book_genres)}
occupation_map = {occupation: i for i, occupation in enumerate(occupations)}

# Add clues as constraints
# Clue 1: Alice is the person who loves fantasy books.
solver.add(house_vars[i]['name'] == name_map['Alice']) == (house_vars[i]['book_genre'] == book_genre_map['fantasy'])

# Clue 2: The person who loves mystery books and Bob are next to each other.
for i in range(1, 6):
    solver.add(Or(
        And(house_vars[i]['book_genre'] == book_genre_map['mystery'], house_vars[i + 1]['name'] == name_map['Bob']),
        And(house_vars[i + 1]['book_genre'] == book_genre_map['mystery'], house_vars[i]['name'] == name_map['Bob'])
    ))

# Clue 3: Carol is the person who loves mystery books.
solver.add(house_vars[i]['name'] == name_map['Carol']) == (house_vars[i]['book_genre'] == book_genre_map['mystery'])

# Clue 4: The person who is a lawyer is the person who loves fantasy books.
solver.add(house_vars[i]['occupation'] == occupation_map['lawyer']) == (house_vars[i]['book_genre'] == book_genre_map['fantasy'])

# Clue 5: Bob is not in the fifth house.
solver.add(house_vars[5]['name'] != name_map['Bob'])

# Clue 6: Arnold is somewhere to the left of the person who is an engineer.
for i in range(1, 6):
    for j in range(i + 1, 7):
        solver.add(Or(house_vars[i]['name'] != name_map['Arnold'], house_vars[j]['occupation'] != occupation_map['engineer']))

# Clue 7: The person who is a nurse is directly left of Alice.
for i in range(1, 6):
    solver.add(And(house_vars[i]['occupation'] == occupation_map['nurse'], house_vars[i + 1]['name'] == name_map['Alice']))

# Clue 8: The person who loves biography books is the person who is a teacher.
solver.add(house_vars[i]['book_genre'] == book_genre_map['biography']) == (house_vars[i]['occupation'] == occupation_map['teacher'])

# Clue 9: The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
for i in range(1, 6):
    for j in range(i + 1, 7):
        solver.add(Or(house_vars[i]['book_genre'] != book_genre_map['historical fiction'], house_vars[j]['occupation'] != occupation_map['teacher']))

# Clue 10: The person who is a doctor is in the first house.
solver.add(house_vars[1]['occupation'] == occupation_map['doctor'])

# Clue 11: The person who loves science fiction books is the person who is an artist.
solver.add(house_vars[i]['book_genre'] == book_genre_map['science fiction']) == (house_vars[i]['occupation'] == occupation_map['artist'])

# Clue 12: Eric is in the third house.
solver.add(house_vars[3]['name'] == name_map['Eric'])

# Clue 13: The person who loves mystery books is not in the fifth house.
solver.add(house_vars[5]['book_genre'] != book_genre_map['mystery'])

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": []
        }
    }
    for i in range(1, 7):
        name = [k for k, v in name_map.items() if v == model[house_vars[i]['name']].as_long()][0]
        book_genre = [k for k, v in book_genre_map.items() if v == model[house_vars[i]['book_genre']].as_long()][0]
        occupation = [k for k, v in occupation_map.items() if v == model[house_vars[i]['occupation']].as_long()][0]
        solution["solution"]["rows"].append([str(i), name, book_genre, occupation])
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")