from z3 import *
import json

# Create Z3 integer variables for each person's house position.
pos_Bob    = Int('pos_Bob')
pos_Arnold = Int('pos_Arnold')
pos_Carol  = Int('pos_Carol')
pos_Alice  = Int('pos_Alice')
pos_Peter  = Int('pos_Peter')
pos_Eric   = Int('pos_Eric')

# Create Z3 integer variables for each book genre's house position.
# (Using the full names for clarity.)
pos_romance            = Int('pos_romance')
pos_historical_fiction = Int('pos_historical_fiction')
pos_biography          = Int('pos_biography')
pos_mystery            = Int('pos_mystery')
pos_fantasy            = Int('pos_fantasy')
pos_science_fiction    = Int('pos_science_fiction')

# Create Z3 integer variables for each occupation's house position.
pos_artist   = Int('pos_artist')
pos_doctor   = Int('pos_doctor')
pos_nurse    = Int('pos_nurse')
pos_engineer = Int('pos_engineer')
pos_teacher  = Int('pos_teacher')
pos_lawyer   = Int('pos_lawyer')

# All houses are numbered 1 to 6.
all_vars = [
    pos_Bob, pos_Arnold, pos_Carol, pos_Alice, pos_Peter, pos_Eric,
    pos_romance, pos_historical_fiction, pos_biography, pos_mystery, pos_fantasy, pos_science_fiction,
    pos_artist, pos_doctor, pos_nurse, pos_engineer, pos_teacher, pos_lawyer
]

# Create the solver and add domain constraints.
solver = Solver()
for var in all_vars:
    solver.add(And(var >= 1, var <= 6))

# Within each category, all positions are different.
solver.add(Distinct(pos_Bob, pos_Arnold, pos_Carol, pos_Alice, pos_Peter, pos_Eric))
solver.add(Distinct(pos_romance, pos_historical_fiction, pos_biography, pos_mystery, pos_fantasy, pos_science_fiction))
solver.add(Distinct(pos_artist, pos_doctor, pos_nurse, pos_engineer, pos_teacher, pos_lawyer))

# Add the clues as constraints.

# Clue 10: "The person who is a doctor is in the first house."
solver.add(pos_doctor == 1)

# Clue 12: "Eric is in the third house."
solver.add(pos_Eric == 3)

# Clue 5: "Bob is not in the fifth house."
solver.add(pos_Bob != 5)

# Clue 1: "Alice is the person who loves fantasy books."
solver.add(pos_Alice == pos_fantasy)

# Clue 4: "The person who is a lawyer is the person who loves fantasy books."
solver.add(pos_lawyer == pos_fantasy)

# Clue 3: "Carol is the person who loves mystery books."
solver.add(pos_Carol == pos_mystery)

# Clue 13: "The person who loves mystery books is not in the fifth house."
solver.add(pos_mystery != 5)

# Clue 2: "The person who loves mystery books and Bob are next to each other."
solver.add(Or(pos_mystery == pos_Bob + 1, pos_mystery == pos_Bob - 1))

# Clue 7: "The person who is a nurse is directly left of Alice."
solver.add(pos_nurse + 1 == pos_Alice)

# Clue 8: "The person who loves biography books is the person who is a teacher."
solver.add(pos_biography == pos_teacher)

# Clue 9: "The person who loves historical fiction books is somewhere to the left of the person who is a teacher."
solver.add(pos_historical_fiction < pos_teacher)

# Clue 11: "The person who loves science fiction books is the person who is an artist."
solver.add(pos_science_fiction == pos_artist)

# Clue 6: "Arnold is somewhere to the left of the person who is an engineer."
solver.add(pos_Arnold < pos_engineer)

# Check the solver for a solution.
if solver.check() == sat:
    m = solver.model()

    # Build mappings from house positions to each attribute.
    # For names:
    name_positions = {
        m.evaluate(pos_Bob).as_long():    "Bob",
        m.evaluate(pos_Arnold).as_long(): "Arnold",
        m.evaluate(pos_Carol).as_long():  "Carol",
        m.evaluate(pos_Alice).as_long():  "Alice",
        m.evaluate(pos_Peter).as_long():  "Peter",
        m.evaluate(pos_Eric).as_long():   "Eric"
    }

    # For book genres:
    book_positions = {
        m.evaluate(pos_romance).as_long():            "romance",
        m.evaluate(pos_historical_fiction).as_long(): "historical fiction",
        m.evaluate(pos_biography).as_long():          "biography",
        m.evaluate(pos_mystery).as_long():            "mystery",
        m.evaluate(pos_fantasy).as_long():            "fantasy",
        m.evaluate(pos_science_fiction).as_long():    "science fiction"
    }

    # For occupations:
    occupation_positions = {
        m.evaluate(pos_artist).as_long():   "artist",
        m.evaluate(pos_doctor).as_long():   "doctor",
        m.evaluate(pos_nurse).as_long():    "nurse",
        m.evaluate(pos_engineer).as_long(): "engineer",
        m.evaluate(pos_teacher).as_long():  "teacher",
        m.evaluate(pos_lawyer).as_long():   "lawyer"
    }

    # Build the rows for each house from 1 to 6.
    rows = []
    for house in range(1, 7):
        row = [
            str(house),
            name_positions.get(house, ""),
            book_positions.get(house, ""),
            occupation_positions.get(house, "")
        ]
        rows.append(row)

    # Build the final JSON object.
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": rows
        }
    }
    
    # Print the JSON-formatted solution.
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")