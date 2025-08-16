from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4]

# Define attributes
names = ["Peter", "Alice", "Eric", "Arnold"]
hobbies = ["cooking", "painting", "gardening", "photography"]
animals = ["horse", "fish", "cat", "bird"]
book_genres = ["fantasy", "mystery", "romance", "science fiction"]
birthday_months = ["april", "jan", "sept", "feb"]
music_genres = ["pop", "rock", "classical", "jazz"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
hobby = {h: String(f"hobby_{h}") for h in houses}
animal = {h: String(f"animal_{h}") for h in houses}
book_genre = {h: String(f"book_genre_{h}") for h in houses}
birthday = {h: String(f"birthday_{h}") for h in houses}
music = {h: String(f"music_{h}") for h in houses}

# Add constraints that each attribute is one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([hobby[h] == ho for ho in hobbies]))
    s.add(Or([animal[h] == a for a in animals]))
    s.add(Or([book_genre[h] == bg for bg in book_genres]))
    s.add(Or([birthday[h] == bm for bm in birthday_months]))
    s.add(Or([music[h] == m for m in music_genres]))

# Add uniqueness constraints for each attribute across houses
for attr in [name, hobby, animal, book_genre, birthday, music]:
    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(attr[h1] != attr[h2])

# Add constraints based on the clues
# Clue 1: The person who loves cooking is the person who loves romance books.
for h in houses:
    s.add(Implies(hobby[h] == "cooking", book_genre[h] == "romance"))

# Clue 2: The person whose birthday is in February is the person who loves pop music.
for h in houses:
    s.add(Implies(birthday[h] == "feb", music[h] == "pop"))

# Clue 3: Eric is not in the second house.
s.add(name[2] != "Eric")

# Clue 4: The person who loves romance books is not in the fourth house.
s.add(book_genre[4] != "romance")

# Clue 5: The person whose birthday is in February is the fish enthusiast.
for h in houses:
    s.add(Implies(birthday[h] == "feb", animal[h] == "fish"))

# Clue 6: Alice is somewhere to the right of the person who loves fantasy books.
# Find the house with fantasy and ensure Alice is in a higher-numbered house
s.add(Or(
    And(book_genre[1] == "fantasy", Or(name[2] == "Alice", name[3] == "Alice", name[4] == "Alice")),
    And(book_genre[2] == "fantasy", Or(name[3] == "Alice", name[4] == "Alice")),
    And(book_genre[3] == "fantasy", name[4] == "Alice")
))

# Clue 7: The person who keeps horses is the person who loves rock music.
for h in houses:
    s.add(Implies(animal[h] == "horse", music[h] == "rock"))

# Clue 8: The person who enjoys gardening is the person whose birthday is in April.
for h in houses:
    s.add(Implies(hobby[h] == "gardening", birthday[h] == "april"))

# Clue 9: The person who loves jazz music is the person who loves cooking.
for h in houses:
    s.add(Implies(music[h] == "jazz", hobby[h] == "cooking"))

# Clue 10: The person who loves rock music is the person who loves mystery books.
for h in houses:
    s.add(Implies(music[h] == "rock", book_genre[h] == "mystery"))

# Clue 11: The person who paints as a hobby is directly left of the person who loves romance books.
for h in range(1, 4):
    s.add(Implies(hobby[h] == "painting", book_genre[h+1] == "romance"))

# Clue 12: Peter is the person who loves pop music.
for h in houses:
    s.add(Implies(name[h] == "Peter", music[h] == "pop"))

# Clue 13: The person who enjoys gardening is Arnold.
for h in houses:
    s.add(Implies(hobby[h] == "gardening", name[h] == "Arnold"))

# Clue 14: The person who loves rock music is directly left of the person whose birthday is in January.
for h in range(1, 4):
    s.add(Implies(music[h] == "rock", birthday[h+1] == "jan"))

# Clue 15: The person who loves cooking is not in the third house.
s.add(hobby[3] != "cooking")

# Clue 16: The cat lover is somewhere to the right of the person who keeps horses.
# Find the house with horse and ensure cat is in a higher-numbered house
s.add(Or(
    And(animal[1] == "horse", Or(animal[2] == "cat", animal[3] == "cat", animal[4] == "cat")),
    And(animal[2] == "horse", Or(animal[3] == "cat", animal[4] == "cat")),
    And(animal[3] == "horse", animal[4] == "cat")
))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            str(model.eval(name[h])),
            str(model.eval(hobby[h])),
            str(model.eval(animal[h])),
            str(model.eval(book_genre[h])),
            str(model.eval(birthday[h])),
            str(model.eval(music[h]))
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")