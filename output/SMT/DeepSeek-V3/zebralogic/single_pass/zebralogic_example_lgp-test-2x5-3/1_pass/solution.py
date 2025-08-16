from z3 import *

# Create a solver instance
s = Solver()

# Define the attributes for each house
houses = [1, 2]
names = {'Eric', 'Arnold'}
hobbies = {'gardening', 'photography'}
book_genres = {'science fiction', 'mystery'}
music_genres = {'rock', 'pop'}
birthday_months = {'april', 'sept'}

# Create variables for each attribute in each house
name = {house: String(f'name_{house}') for house in houses}
hobby = {house: String(f'hobby_{house}') for house in houses}
book_genre = {house: String(f'book_genre_{house}') for house in houses}
music_genre = {house: String(f'music_genre_{house}') for house in houses}
birthday = {house: String(f'birthday_{house}') for house in houses}

# Add constraints that all attributes within a category are unique
s.add(Distinct([name[house] for house in houses]))
s.add(Distinct([hobby[house] for house in houses]))
s.add(Distinct([book_genre[house] for house in houses]))
s.add(Distinct([music_genre[house] for house in houses]))
s.add(Distinct([birthday[house] for house in houses]))

# Each attribute must be one of the allowed values
for house in houses:
    s.add(Or([name[house] == StringVal(n) for n in names]))
    s.add(Or([hobby[house] == StringVal(h) for h in hobbies]))
    s.add(Or([book_genre[house] == StringVal(bg) for bg in book_genres]))
    s.add(Or([music_genre[house] == StringVal(mg) for mg in music_genres]))
    s.add(Or([birthday[house] == StringVal(bm) for bm in birthday_months]))

# Add constraints based on the clues
# Clue 2: Arnold is not in the first house.
s.add(name[1] != StringVal('Arnold'))

# Clue 4: The person whose birthday is in April is Arnold.
for house in houses:
    s.add(Implies(birthday[house] == StringVal('april'), name[house] == StringVal('Arnold')))

# Clue 5: The person who loves mystery books is in the first house.
s.add(book_genre[1] == StringVal('mystery'))

# Clue 1: The person who loves mystery books is the person who loves rock music.
s.add(music_genre[1] == StringVal('rock'))

# Clue 3: The person who loves mystery books is the person who enjoys gardening.
s.add(hobby[1] == StringVal('gardening'))

# Solve the model
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": []
        }
    }
    for house in sorted(houses):
        row = [
            str(house),
            str(model.eval(name[house])),
            str(model.eval(hobby[house])),
            str(model.eval(book_genre[house])),
            str(model.eval(music_genre[house])),
            str(model.eval(birthday[house]))
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")