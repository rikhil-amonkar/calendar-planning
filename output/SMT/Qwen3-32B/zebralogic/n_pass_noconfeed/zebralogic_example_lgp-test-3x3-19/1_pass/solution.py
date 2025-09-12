from z3 import *
import json

# Define EnumSorts for each attribute category
Names, (Eric, Arnold, Peter) = EnumSort('Names', ['Eric', 'Arnold', 'Peter'])
Smoothies, (desert, watermelon, cherry) = EnumSort('Smoothies', ['desert', 'watermelon', 'cherry'])
Genres, (science_fiction, romance, mystery) = EnumSort('Genres', ['science_fiction', 'romance', 'mystery'])

# Create variables for each house's attributes
name1, name2, name3 = Consts('name1 name2 name3', Names)
smoothie1, smoothie2, smoothie3 = Consts('smoothie1 smoothie2 smoothie3', Smoothies)
genre1, genre2, genre3 = Consts('genre1 genre2 genre3', Genres)

s = Solver()

# Add uniqueness constraints for each attribute category
s.add(Distinct(name1, name2, name3))
s.add(Distinct(smoothie1, smoothie2, smoothie3))
s.add(Distinct(genre1, genre2, genre3))

# Clue 5: Peter is in the first house
s.add(name1 == Peter)

# Clue 2: Arnold loves mystery books
s.add(Implies(name1 == Arnold, genre1 == mystery))
s.add(Implies(name2 == Arnold, genre2 == mystery))
s.add(Implies(name3 == Arnold, genre3 == mystery))

# Clue 4: Desert smoothie lover is directly left of mystery book lover
s.add(Implies(name2 == Arnold, smoothie1 == desert))
s.add(Implies(name3 == Arnold, smoothie2 == desert))

# Clue 1: Cherry smoothie lover is somewhere left of mystery book lover
s.add(Implies(name2 == Arnold, smoothie1 == cherry))
s.add(Implies(name3 == Arnold, Or(smoothie1 == cherry, smoothie2 == cherry)))

# Clue 3: Science fiction book lover is not in the first house
s.add(genre1 != science_fiction)

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    solution = []
    for i, n, s_smoothie, g in [(1, name1, smoothie1, genre1),
                                (2, name2, smoothie2, genre2),
                                (3, name3, smoothie3, genre3)]:
        name_val = model.eval(n).decl().name()
        smoothie_val = model.eval(s_smoothie).decl().name()
        genre_val = model.eval(g).decl().name()
        # Convert 'science_fiction' to 'science fiction' for output
        if genre_val == 'science_fiction':
            genre_val = 'science fiction'
        solution.append([str(i), name_val, smoothie_val, genre_val])
    
    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "BookGenre"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")