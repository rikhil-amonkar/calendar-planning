from z3 import *

def main():
    # Define the enums for attributes
    Name, names = EnumSort('Name', ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric'])
    Bob, Arnold, Carol, Alice, Peter, Eric = names

    Genre, genres = EnumSort('Genre', [
        'romance', 
        'historical fiction', 
        'biography', 
        'mystery', 
        'fantasy', 
        'science fiction'
    ])
    romance, historical_fiction, biography, mystery, fantasy, science_fiction = genres

    Occupation, occupations = EnumSort('Occupation', [
        'artist', 
        'doctor', 
        'nurse', 
        'engineer', 
        'teacher', 
        'lawyer'
    ])
    artist, doctor, nurse, engineer, teacher, lawyer = occupations

    # Create arrays for attributes for houses 1 to 6 (index 0 to 5)
    n = [Const('n%d' % i, Name) for i in range(1, 7)]  # names
    g = [Const('g%d' % i, Genre) for i in range(1, 7)]  # genres
    o = [Const('o%d' % i, Occupation) for i in range(1, 7)]  # occupations

    s = Solver()

    # All attributes must be distinct
    s.add(Distinct(n))
    s.add(Distinct(g))
    s.add(Distinct(o))

    # Clue 1: Alice is the person who loves fantasy books.
    for i in range(6):
        s.add(Implies(g[i] == fantasy, n[i] == Alice))

    # Clue 4: The person who is a lawyer is the person who loves fantasy books.
    for i in range(6):
        s.add(Implies(g[i] == fantasy, o[i] == lawyer))

    # Clue 3: Carol is the person who loves mystery books.
    for i in range(6):
        s.add(Implies(g[i] == mystery, n[i] == Carol))

    # Clue 2: The person who loves mystery books and Bob are next to each other.
    for i in range(6):
        if i == 0:
            s.add(Implies(g[i] == mystery, n[i+1] == Bob))
        elif i == 5:
            s.add(Implies(g[i] == mystery, n[i-1] == Bob))
        else:
            s.add(Implies(g[i] == mystery, Or(n[i-1] == Bob, n[i+1] == Bob)))
    
    for i in range(6):
        if i == 0:
            s.add(Implies(n[i] == Bob, g[i+1] == mystery))
        elif i == 5:
            s.add(Implies(n[i] == Bob, g[i-1] == mystery))
        else:
            s.add(Implies(n[i] == Bob, Or(g[i-1] == mystery, g[i+1] == mystery)))

    # Clue 5: Bob is not in the fifth house (index 4)
    s.add(n[4] != Bob)

    # Clue 6: Arnold is to the left of the engineer.
    for i in range(6):
        # If Arnold is in house i, then engineer must be in a house j>i
        s.add(Implies(n[i] == Arnold, Or([o[j] == engineer for j in range(i+1, 6)])))

    # Clue 7: The nurse is directly left of Alice.
    for i in range(5):
        s.add(Implies(o[i] == nurse, n[i+1] == Alice))
    for i in range(1, 6):
        s.add(Implies(n[i] == Alice, o[i-1] == nurse))

    # Clue 8: The person who loves biography books is the teacher.
    for i in range(6):
        s.add(Implies(g[i] == biography, o[i] == teacher))

    # Clue 9: The person who loves historical fiction is to the left of the teacher.
    for i in range(6):
        s.add(Implies(g[i] == historical_fiction, Or([o[j] == teacher for j in range(i+1, 6)])))

    # Clue 10: The doctor is in the first house (index 0)
    s.add(o[0] == doctor)

    # Clue 11: The person who loves science fiction is the artist.
    for i in range(6):
        s.add(Implies(g[i] == science_fiction, o[i] == artist))

    # Clue 12: Eric is in the third house (index 2)
    s.add(n[2] == Eric)

    # Clue 13: The person who loves mystery books is not in the fifth house (index 4)
    s.add(g[4] != mystery)

    # Alice cannot be in house1 (because nurse must be left of Alice, and house1 has no left neighbor)
    s.add(n[0] != Alice)

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        rows = []
        for i in range(6):
            house_num = str(i+1)
            name_val = model.eval(n[i])
            genre_val = model.eval(g[i])
            occup_val = model.eval(o[i])
            # Convert to string (Z3 enum values are printed as their names)
            name_str = str(name_val)
            genre_str = str(genre_val)
            occup_str = str(occup_val)
            rows.append([house_num, name_str, genre_str, occup_str])
        
        # Create the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Occupation"],
                "rows": rows
            }
        }
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()