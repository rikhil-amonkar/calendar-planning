from z3 import *
import json

# Define EnumSorts for each attribute
Names, (Peter, Alice, Eric, Arnold) = EnumSort('Names', ['Peter', 'Alice', 'Eric', 'Arnold'])
Hobbies, (Cooking, Painting, Gardening, Photography) = EnumSort('Hobbies', ['cooking', 'painting', 'gardening', 'photography'])
Animals, (Horse, Fish, Cat, Bird) = EnumSort('Animals', ['horse', 'fish', 'cat', 'bird'])
BookGenres, (Fantasy, Mystery, Romance, ScienceFiction) = EnumSort('BookGenres', ['fantasy', 'mystery', 'romance', 'science_fiction'])
Birthdays, (April, Jan, Sept, Feb) = EnumSort('Birthdays', ['april', 'jan', 'sept', 'feb'])
MusicGenres, (Pop, Rock, Classical, Jazz) = EnumSort('MusicGenres', ['pop', 'rock', 'classical', 'jazz'])

# Create variables for each house (1-4)
n1, n2, n3, n4 = Consts('n1 n2 n3 n4', Names)
h1, h2, h3, h4 = Consts('h1 h2 h3 h4', Hobbies)
a1, a2, a3, a4 = Consts('a1 a2 a3 a4', Animals)
bg1, bg2, bg3, bg4 = Consts('bg1 bg2 bg3 bg4', BookGenres)
d1, d2, d3, d4 = Consts('d1 d2 d3 d4', Birthdays)
m1, m2, m3, m4 = Consts('m1 m2 m3 m4', MusicGenres)

s = Solver()

# Add distinct constraints for each attribute
s.add(Distinct(n1, n2, n3, n4))
s.add(Distinct(h1, h2, h3, h4))
s.add(Distinct(a1, a2, a3, a4))
s.add(Distinct(bg1, bg2, bg3, bg4))
s.add(Distinct(d1, d2, d3, d4))
s.add(Distinct(m1, m2, m3, m4))

# Add constraints based on clues
# Clue 1: Cooking and Romance
s.add((h1 == Cooking) == (bg1 == Romance))
s.add((h2 == Cooking) == (bg2 == Romance))
s.add((h3 == Cooking) == (bg3 == Romance))
s.add((h4 == Cooking) == (bg4 == Romance))

# Clue 2: Feb and Pop
s.add((d1 == Feb) == (m1 == Pop))
s.add((d2 == Feb) == (m2 == Pop))
s.add((d3 == Feb) == (m3 == Pop))
s.add((d4 == Feb) == (m4 == Pop))

# Clue 3: Eric not in second house
s.add(n2 != Eric)

# Clue 4: Romance not in fourth house
s.add(bg4 != Romance)

# Clue 5: Feb and Fish
s.add((d1 == Feb) == (a1 == Fish))
s.add((d2 == Feb) == (a2 == Fish))
s.add((d3 == Feb) == (a3 == Fish))
s.add((d4 == Feb) == (a4 == Fish))

# Clue 6: Alice to the right of fantasy
pos_fantasy = If(bg1 == Fantasy, 1, If(bg2 == Fantasy, 2, If(bg3 == Fantasy, 3, 4)))
pos_alice = If(n1 == Alice, 1, If(n2 == Alice, 2, If(n3 == Alice, 3, 4)))
s.add(pos_alice > pos_fantasy)

# Clue 7: Horse and Rock
s.add((a1 == Horse) == (m1 == Rock))
s.add((a2 == Horse) == (m2 == Rock))
s.add((a3 == Horse) == (m3 == Rock))
s.add((a4 == Horse) == (m4 == Rock))

# Clue 8: Gardening and April
s.add((h1 == Gardening) == (d1 == April))
s.add((h2 == Gardening) == (d2 == April))
s.add((h3 == Gardening) == (d3 == April))
s.add((h4 == Gardening) == (d4 == April))

# Clue 9: Jazz and Cooking
s.add((m1 == Jazz) == (h1 == Cooking))
s.add((m2 == Jazz) == (h2 == Cooking))
s.add((m3 == Jazz) == (h3 == Cooking))
s.add((m4 == Jazz) == (h4 == Cooking))

# Clue 10: Rock and Mystery
s.add((m1 == Rock) == (bg1 == Mystery))
s.add((m2 == Rock) == (bg2 == Mystery))
s.add((m3 == Rock) == (bg3 == Mystery))
s.add((m4 == Rock) == (bg4 == Mystery))

# Clue 11: Painter left of romance
s.add(Or(
    And(h1 == Painting, bg2 == Romance),
    And(h2 == Painting, bg3 == Romance),
    And(h3 == Painting, bg4 == Romance)
))

# Clue 12: Peter and Pop
s.add((n1 == Peter) == (m1 == Pop))
s.add((n2 == Peter) == (m2 == Pop))
s.add((n3 == Peter) == (m3 == Pop))
s.add((n4 == Peter) == (m4 == Pop))

# Clue 13: Gardening is Arnold
s.add((h1 == Gardening) == (n1 == Arnold))
s.add((h2 == Gardening) == (n2 == Arnold))
s.add((h3 == Gardening) == (n3 == Arnold))
s.add((h4 == Gardening) == (n4 == Arnold))

# Clue 14: Rock left of Jan
s.add(Or(
    And(m1 == Rock, d2 == Jan),
    And(m2 == Rock, d3 == Jan),
    And(m3 == Rock, d4 == Jan)
))

# Clue 15: Cooking not in third house
s.add(h3 != Cooking)

# Clue 16: Cat to the right of Horse
pos_horse = If(a1 == Horse, 1, If(a2 == Horse, 2, If(a3 == Horse, 3, 4)))
pos_cat = If(a1 == Cat, 1, If(a2 == Cat, 2, If(a3 == Cat, 3, 4)))
s.add(pos_cat > pos_horse)

# Check for solution
if s.check() == sat:
    model = s.model()
    # Prepare the rows
    names = [n1, n2, n3, n4]
    hobbies = [h1, h2, h3, h4]
    animals = [a1, a2, a3, a4]
    book_genres = [bg1, bg2, bg3, bg4]
    birthdays_list = [d1, d2, d3, d4]
    music_genres = [m1, m2, m3, m4]
    
    rows = []
    for idx in range(4):
        house_num = idx + 1
        name = model.eval(names[idx]).decl().name()
        hobby = model.eval(hobbies[idx]).decl().name()
        animal = model.eval(animals[idx]).decl().name()
        book_genre = model.eval(book_genres[idx]).decl().name()
        birthday = model.eval(birthdays_list[idx]).decl().name()
        music_genre = model.eval(music_genres[idx]).decl().name()
        
        # Replace 'science_fiction' with 'science fiction'
        if book_genre == 'science_fiction':
            book_genre = 'science fiction'
        
        rows.append([
            str(house_num),
            name,
            hobby,
            animal,
            book_genre,
            birthday,
            music_genre
        ])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")