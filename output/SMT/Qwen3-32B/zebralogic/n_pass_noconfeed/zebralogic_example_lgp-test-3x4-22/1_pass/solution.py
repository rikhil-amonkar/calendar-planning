from z3 import *
import json

# Define EnumSorts for each attribute
Name, (Arnold, Eric, Peter) = EnumSort('Name', ['Arnold', 'Eric', 'Peter'])
MusicGenre, (pop, rock, classical) = EnumSort('MusicGenre', ['pop', 'rock', 'classical'])
Children, (Fred, Meredith, Bella) = EnumSort('Children', ['Fred', 'Meredith', 'Bella'])
BookGenre, (mystery, romance, science_fiction) = EnumSort('BookGenre', ['mystery', 'romance', 'science fiction'])

houses = 3

# Create variables for each house's attributes
names = [Const(f'name_{i+1}', Name) for i in range(houses)]
musics = [Const(f'music_{i+1}', MusicGenre) for i in range(houses)]
childrens = [Const(f'child_{i+1}', Children) for i in range(houses)]
books = [Const(f'book_{i+1}', BookGenre) for i in range(houses)]

s = Solver()

# Add uniqueness constraints for each attribute
s.add(Distinct(names))
s.add(Distinct(musics))
s.add(Distinct(childrens))
s.add(Distinct(books))

# Add clues as constraints
# Clue 2: Peter is in the first house.
s.add(names[0] == Peter)

# Clue 5: Eric is the person who loves mystery books.
s.add(Or([And(books[i] == mystery, names[i] == Eric) for i in range(houses)]))

# Clue 3: The person who loves mystery books loves classical music.
s.add(Or([And(books[i] == mystery, musics[i] == classical) for i in range(houses)]))

# Clue 1: The person whose child is Fred is directly left of the person who loves mystery books.
s.add(Or(
    And(childrens[0] == Fred, books[1] == mystery),
    And(childrens[1] == Fred, books[2] == mystery)
))

# Clue 4: The person who loves science fiction books has child Meredith.
s.add(Or([And(books[i] == science_fiction, childrens[i] == Meredith) for i in range(houses)]))

# Clue 6: Rock music is to the right of romance books.
s.add(Or(
    And(books[0] == romance, Or(musics[1] == rock, musics[2] == rock)),
    And(books[1] == romance, musics[2] == rock)
))

# Check for solution
if s.check() == sat:
    model = s.model()
    rows = []
    for i in range(houses):
        house_num = str(i + 1)
        name_val = model.evaluate(names[i]).name()
        music_val = model.evaluate(musics[i]).name()
        child_val = model.evaluate(childrens[i]).name()
        book_val = model.evaluate(books[i]).name()
        rows.append([house_num, name_val, music_val, child_val, book_val])
    solution = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")