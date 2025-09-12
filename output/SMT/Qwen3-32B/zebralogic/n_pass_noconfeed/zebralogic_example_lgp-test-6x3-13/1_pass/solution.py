from z3 import *
import json

def solve_puzzle():
    s = Solver()

    # Define variables for each person's house
    bob_house = Int('bob_house')
    arnold_house = Int('arnold_house')
    carol_house = Int('carol_house')
    alice_house = Int('alice_house')
    peter_house = Int('peter_house')
    eric_house = Int('eric_house')

    # Define variables for each book genre's house
    romance_house = Int('romance_house')
    historical_fiction_house = Int('historical_fiction_house')
    biography_house = Int('biography_house')
    mystery_house = Int('mystery_house')
    fantasy_house = Int('fantasy_house')
    science_fiction_house = Int('science_fiction_house')

    # Define variables for each occupation's house
    artist_house = Int('artist_house')
    doctor_house = Int('doctor_house')
    nurse_house = Int('nurse_house')
    engineer_house = Int('engineer_house')
    teacher_house = Int('teacher_house')
    lawyer_house = Int('lawyer_house')

    # Add constraints that all are between 1 and 6
    for var in [bob_house, arnold_house, carol_house, alice_house, peter_house, eric_house]:
        s.add(And(1 <= var, var <= 6))

    for var in [romance_house, historical_fiction_house, biography_house, mystery_house, fantasy_house, science_fiction_house]:
        s.add(And(1 <= var, var <= 6))

    for var in [artist_house, doctor_house, nurse_house, engineer_house, teacher_house, lawyer_house]:
        s.add(And(1 <= var, var <= 6))

    # Add distinctness constraints
    s.add(Distinct([bob_house, arnold_house, carol_house, alice_house, peter_house, eric_house]))
    s.add(Distinct([romance_house, historical_fiction_house, biography_house, mystery_house, fantasy_house, science_fiction_house]))
    s.add(Distinct([artist_house, doctor_house, nurse_house, engineer_house, teacher_house, lawyer_house]))

    # Add the clues as constraints
    s.add(alice_house == fantasy_house)  # Clue 1
    s.add(Abs(mystery_house - bob_house) == 1)  # Clue 2
    s.add(carol_house == mystery_house)  # Clue 3
    s.add(lawyer_house == fantasy_house)  # Clue 4
    s.add(bob_house != 5)  # Clue 5
    s.add(arnold_house < engineer_house)  # Clue 6
    s.add(nurse_house + 1 == alice_house)  # Clue 7
    s.add(biography_house == teacher_house)  # Clue 8
    s.add(historical_fiction_house < teacher_house)  # Clue 9
    s.add(doctor_house == 1)  # Clue 10
    s.add(science_fiction_house == artist_house)  # Clue 11
    s.add(eric_house == 3)  # Clue 12
    s.add(mystery_house != 5)  # Clue 13

    if s.check() == sat:
        model = s.model()

        # Process names
        name_to_house = {
            'Bob': model.eval(bob_house).as_long(),
            'Arnold': model.eval(arnold_house).as_long(),
            'Carol': model.eval(carol_house).as_long(),
            'Alice': model.eval(alice_house).as_long(),
            'Peter': model.eval(peter_house).as_long(),
            'Eric': model.eval(eric_house).as_long(),
        }
        house_to_name = {v: k for k, v in name_to_house.items()}

        # Process books
        book_to_house = {
            'romance': model.eval(romance_house).as_long(),
            'historical fiction': model.eval(historical_fiction_house).as_long(),
            'biography': model.eval(biography_house).as_long(),
            'mystery': model.eval(mystery_house).as_long(),
            'fantasy': model.eval(fantasy_house).as_long(),
            'science fiction': model.eval(science_fiction_house).as_long(),
        }
        house_to_book = {v: k for k, v in book_to_house.items()}

        # Process occupations
        occupation_to_house = {
            'artist': model.eval(artist_house).as_long(),
            'doctor': model.eval(doctor_house).as_long(),
            'nurse': model.eval(nurse_house).as_long(),
            'engineer': model.eval(engineer_house).as_long(),
            'teacher': model.eval(teacher_house).as_long(),
            'lawyer': model.eval(lawyer_house).as_long(),
        }
        house_to_occupation = {v: k for k, v in occupation_to_house.items()}

        # Build the solution rows
        rows = []
        for h in range(1, 7):
            row = [
                str(h),
                house_to_name[h],
                house_to_book[h],
                house_to_occupation[h]
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Occupation"],
                "rows": rows
            }
        }
        return json.dumps(solution, indent=2)
    else:
        return json.dumps({"error": "No solution found"})

if __name__ == "__main__":
    print(solve_puzzle())