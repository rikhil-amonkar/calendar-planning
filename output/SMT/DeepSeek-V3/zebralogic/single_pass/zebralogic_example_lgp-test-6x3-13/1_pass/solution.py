from z3 import *

def solve_housing_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the attributes
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']

    # Create variables for each attribute in each house
    name = {h: String(f'name_{h}') for h in houses}
    genre = {h: String(f'genre_{h}') for h in houses}
    occupation = {h: String(f'occupation_{h}') for h in houses}

    # Add constraints that all names, genres, and occupations are unique and one of the allowed values
    for h in houses:
        s.add(Or([name[h] == n for n in names]))
        s.add(Or([genre[h] == g for g in genres]))
        s.add(Or([occupation[h] == o for o in occupations]))

    for h1 in houses:
        for h2 in houses:
            if h1 < h2:
                s.add(name[h1] != name[h2])
                s.add(genre[h1] != genre[h2])
                s.add(occupation[h1] != occupation[h2])

    # Clue 10: The person who is a doctor is in the first house.
    s.add(occupation[1] == 'doctor')

    # Clue 12: Eric is in the third house.
    s.add(name[3] == 'Eric')

    # Clue 1: Alice is the person who loves fantasy books.
    for h in houses:
        s.add(Implies(name[h] == 'Alice', genre[h] == 'fantasy'))

    # Clue 3: Carol is the person who loves mystery books.
    for h in houses:
        s.add(Implies(name[h] == 'Carol', genre[h] == 'mystery'))

    # Clue 4: The person who is a lawyer is the person who loves fantasy books.
    for h in houses:
        s.add(Implies(occupation[h] == 'lawyer', genre[h] == 'fantasy'))
        s.add(Implies(genre[h] == 'fantasy', occupation[h] == 'lawyer'))

    # Clue 5: Bob is not in the fifth house.
    s.add(name[5] != 'Bob')

    # Clue 6: Arnold is somewhere to the left of the person who is an engineer.
    # This means Arnold is in a house with a smaller number than the engineer.
    engineer_house = Int('engineer_house')
    s.add(Or([occupation[h] == 'engineer' for h in houses]))
    for h in houses:
        s.add(Implies(occupation[h] == 'engineer', engineer_house == h))
    arnold_house = Int('arnold_house')
    for h in houses:
        s.add(Implies(name[h] == 'Arnold', arnold_house == h))
    s.add(arnold_house < engineer_house)

    # Clue 7: The person who is a nurse is directly left of Alice.
    # This means nurse is in house h, Alice is in house h+1.
    for h in range(1, 6):
        s.add(Implies(occupation[h] == 'nurse', name[h+1] == 'Alice'))

    # Clue 8: The person who loves biography books is the person who is a teacher.
    for h in houses:
        s.add(Implies(genre[h] == 'biography', occupation[h] == 'teacher'))
        s.add(Implies(occupation[h] == 'teacher', genre[h] == 'biography'))

    # Clue 9: The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
    # Historical fiction is in a house with a smaller number than the teacher.
    teacher_house = Int('teacher_house')
    for h in houses:
        s.add(Implies(occupation[h] == 'teacher', teacher_house == h))
    historical_house = Int('historical_house')
    for h in houses:
        s.add(Implies(genre[h] == 'historical fiction', historical_house == h))
    s.add(historical_house < teacher_house)

    # Clue 11: The person who loves science fiction books is the person who is an artist.
    for h in houses:
        s.add(Implies(genre[h] == 'science fiction', occupation[h] == 'artist'))
        s.add(Implies(occupation[h] == 'artist', genre[h] == 'science fiction'))

    # Clue 2: The person who loves mystery books and Bob are next to each other.
    # This means mystery is in h, Bob is in h+1 or h-1, or vice versa.
    mystery_house = Int('mystery_house')
    for h in houses:
        s.add(Implies(genre[h] == 'mystery', mystery_house == h))
    bob_house = Int('bob_house')
    for h in houses:
        s.add(Implies(name[h] == 'Bob', bob_house == h))
    s.add(Or(bob_house == mystery_house + 1, bob_house == mystery_house - 1))

    # Clue 13: The person who loves mystery books is not in the fifth house.
    s.add(genre[5] != 'mystery')

    # Check if the solver can find a solution
    if s.check() == sat:
        m = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Occupation"],
                "rows": []
            }
        }
        for h in sorted(houses):
            row = [
                str(h),
                m.evaluate(name[h]).as_string(),
                m.evaluate(genre[h]).as_string(),
                m.evaluate(occupation[h]).as_string()
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"solution": {"header": [], "rows": []}}

# Print the solution as JSON
import json
print(json.dumps(solve_housing_problem(), indent=2))