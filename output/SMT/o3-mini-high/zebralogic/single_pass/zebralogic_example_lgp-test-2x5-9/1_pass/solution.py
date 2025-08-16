from z3 import *
import json

# Create solver instance
s = Solver()

# Define variables for each house.
# For each attribute, 0 and 1 represent the two possibilities:
# Mapping:
#   Name: 0 = "Arnold", 1 = "Eric"
#   BookGenre: 0 = "mystery", 1 = "science fiction"
#   Vacation: 0 = "mountain", 1 = "beach"
#   Animal: 0 = "cat", 1 = "horse"
#   MusicGenre: 0 = "rock", 1 = "pop"

name1 = Int('name1')
name2 = Int('name2')
book1 = Int('book1')
book2 = Int('book2')
vacation1 = Int('vacation1')
vacation2 = Int('vacation2')
animal1 = Int('animal1')
animal2 = Int('animal2')
music1 = Int('music1')
music2 = Int('music2')

# Add domain constraints: each variable can only be 0 or 1.
vars = [name1, name2, book1, book2, vacation1, vacation2, animal1, animal2, music1, music2]
for var in vars:
    s.add(Or(var == 0, var == 1))

# Add distinct constraints for each attribute category (each house gets a unique value)
s.add(Distinct(name1, name2))
s.add(Distinct(book1, book2))
s.add(Distinct(vacation1, vacation2))
s.add(Distinct(animal1, animal2))
s.add(Distinct(music1, music2))

# Clues:

# 1. The person who loves beach vacations is Eric.
#    Equivalently, for a given house: (vacation == beach (1)) <-> (name == Eric (1)).
s.add((vacation1 == 1) == (name1 == 1))
s.add((vacation2 == 1) == (name2 == 1))

# 2. The person who loves pop music is the person who loves beach vacations.
#    Equivalently: (vacation == beach (1)) <-> (music == pop (1)).
s.add((vacation1 == 1) == (music1 == 1))
s.add((vacation2 == 1) == (music2 == 1))

# 3. The person who loves rock music is the person who loves mystery books.
#    With our mapping, rock music is 0 and mystery is 0.
#    So, (music == rock (0)) <-> (book == mystery (0)).
s.add((music1 == 0) == (book1 == 0))
s.add((music2 == 0) == (book2 == 0))

# 5. The person who loves mystery books is in the first house.
s.add(book1 == 0)

# 4. The cat lover is not in the second house.
#    With our mapping, cat is 0 so animal2 must not be 0, hence it must be 1.
s.add(animal2 != 0)

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    
    # Define mappings to convert Z3 model integers to actual attributes.
    names = ["Arnold", "Eric"]
    books = ["mystery", "science fiction"]
    vacations = ["mountain", "beach"]
    animals = ["cat", "horse"]
    music_genres = ["rock", "pop"]
    
    # Construct the rows for house 1 and house 2.
    row1 = ["1",
            names[m[name1].as_long()],
            books[m[book1].as_long()],
            vacations[m[vacation1].as_long()],
            animals[m[animal1].as_long()],
            music_genres[m[music1].as_long()]]
    
    row2 = ["2",
            names[m[name2].as_long()],
            books[m[book2].as_long()],
            vacations[m[vacation2].as_long()],
            animals[m[animal2].as_long()],
            music_genres[m[music2].as_long()]]
    
    result = {
      "solution": {
          "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
          "rows": [row1, row2]
      }
    }
    
    # Print the JSON-formatted solution.
    print(json.dumps(result))
else:
    print("No solution found")