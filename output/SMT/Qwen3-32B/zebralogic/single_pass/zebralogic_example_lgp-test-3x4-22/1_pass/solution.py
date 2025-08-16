from z3 import *
import json

# Define EnumSorts
Name, (Arnold, Eric, Peter) = EnumSort('Name', ['Arnold', 'Eric', 'Peter'])
Music, (pop, rock, classical) = EnumSort('Music', ['pop', 'rock', 'classical'])
Child, (Fred, Meredith, Bella) = EnumSort('Child', ['Fred', 'Meredith', 'Bella'])
Book, (mystery, romance, science_fiction) = EnumSort('Book', ['mystery', 'romance', 'science fiction'])

# Create variables for each house
name1, name2, name3 = Consts('name1 name2 name3', Name)
music1, music2, music3 = Consts('music1 music2 music3', Music)
child1, child2, child3 = Consts('child1 child2 child3', Child)
book1, book2, book3 = Consts('book1 book2 book3', Book)

s = Solver()

# Add uniqueness constraints
s.add(Distinct(name1, name2, name3))
s.add(Distinct(music1, music2, music3))
s.add(Distinct(child1, child2, child3))
s.add(Distinct(book1, book2, book3))

# Add clues
# Clue 2: Peter is in first house
s.add(name1 == Peter)

# Clue 5: Eric loves mystery books
s.add(Or(
    And(name1 == Eric, book1 == mystery),
    And(name2 == Eric, book2 == mystery),
    And(name3 == Eric, book3 == mystery)
))

# Clue 3: mystery book lover loves classical music
s.add(Or(
    And(book1 == mystery, music1 == classical),
    And(book2 == mystery, music2 == classical),
    And(book3 == mystery, music3 == classical)
))

# Clue 1: Fred's house is directly left of mystery book
s.add(Or(
    And(child1 == Fred, book2 == mystery),
    And(child2 == Fred, book3 == mystery)
))

# Clue 4: science fiction book has child Meredith
s.add(Or(
    And(book1 == science_fiction, child1 == Meredith),
    And(book2 == science_fiction, child2 == Meredith),
    And(book3 == science_fiction, child3 == Meredith)
))

# Clue 6: rock is to the right of romance
s.add(music1 != rock)
s.add(Implies(music2 == rock, book1 == romance))
s.add(Implies(music3 == rock, Or(book1 == romance, book2 == romance)))

if s.check() == sat:
    model = s.model()
    names = [name1, name2, name3]
    musics = [music1, music2, music3]
    childrens = [child1, child2, child3]
    books = [book1, book2, book3]
    rows = []
    for i in range(3):
        house_num = i + 1
        name_val = model.eval(names[i]).as_string()
        music_val = model.eval(musics[i]).as_string()
        child_val = model.eval(childrens[i]).as_string()
        book_val = model.eval(books[i]).as_string()
        rows.append([str(house_num), name_val, music_val, child_val, book_val])
    solution = {
        "solution": {
            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")