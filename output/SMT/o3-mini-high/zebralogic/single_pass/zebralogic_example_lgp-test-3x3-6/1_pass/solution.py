from z3 import *
import json

def main():
    s = Solver()

    # Define house positions for each person (1, 2, 3)
    Eric_pos = Int('Eric_pos')
    Arnold_pos = Int('Arnold_pos')
    Peter_pos = Int('Peter_pos')

    # Define book genres for each person:
    # 1 = "mystery", 2 = "science fiction", 3 = "romance"
    Eric_book = Int('Eric_book')
    Arnold_book = Int('Arnold_book')
    Peter_book = Int('Peter_book')

    # Define vacation preferences for each person:
    # 1 = "mountain", 2 = "beach", 3 = "city"
    Eric_vac = Int('Eric_vac')
    Arnold_vac = Int('Arnold_vac')
    Peter_vac = Int('Peter_vac')

    # Domain constraints for houses, books and vacations (values between 1 and 3)
    s.add(And(Eric_pos >= 1, Eric_pos <= 3))
    s.add(And(Arnold_pos >= 1, Arnold_pos <= 3))
    s.add(And(Peter_pos >= 1, Peter_pos <= 3))

    s.add(And(Eric_book >= 1, Eric_book <= 3))
    s.add(And(Arnold_book >= 1, Arnold_book <= 3))
    s.add(And(Peter_book >= 1, Peter_book <= 3))

    s.add(And(Eric_vac >= 1, Eric_vac <= 3))
    s.add(And(Arnold_vac >= 1, Arnold_vac <= 3))
    s.add(And(Peter_vac >= 1, Peter_vac <= 3))

    # All-different constraints (each attribute assignment is unique)
    s.add(Distinct(Eric_pos, Arnold_pos, Peter_pos))
    s.add(Distinct(Eric_book, Arnold_book, Peter_book))
    s.add(Distinct(Eric_vac, Arnold_vac, Peter_vac))

    # Clue 1: Eric is directly left of Arnold.
    s.add(Arnold_pos == Eric_pos + 1)

    # Clue 3: Peter is the person who prefers city breaks.
    s.add(Peter_vac == 3)

    # Clue 5: The person who loves science fiction books is the person who loves beach vacations.
    # Enforce equivalence for each person between having "science fiction" (2) and "beach" (2)
    s.add(Implies(Eric_book == 2, Eric_vac == 2))
    s.add(Implies(Eric_vac == 2, Eric_book == 2))
    s.add(Implies(Arnold_book == 2, Arnold_vac == 2))
    s.add(Implies(Arnold_vac == 2, Arnold_book == 2))
    s.add(Implies(Peter_book == 2, Peter_vac == 2))
    s.add(Implies(Peter_vac == 2, Peter_book == 2))

    # Clue 2: Peter is somewhere to the right of the person who loves beach vacations.
    # (Only Eric or Arnold can be the beach person because Peter_vac is already set to 3)
    s.add(Implies(Eric_vac == 2, Eric_pos < Peter_pos))
    s.add(Implies(Arnold_vac == 2, Arnold_pos < Peter_pos))

    # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
    # Determine the house of the mystery-lover and the beach-lover using nested If’s.
    pos_mystery = If(Eric_book == 1, Eric_pos, If(Arnold_book == 1, Arnold_pos, Peter_pos))
    pos_beach = If(Eric_vac == 2, Eric_pos, If(Arnold_vac == 2, Arnold_pos, Peter_pos))
    s.add(pos_mystery < pos_beach)

    # Solve the constraints
    if s.check() == sat:
        m = s.model()

        # Mapping dictionaries for decoding numbers to strings.
        book_mapping = {1: "mystery", 2: "science fiction", 3: "romance"}
        vacation_mapping = {1: "mountain", 2: "beach", 3: "city"}

        # Collect the details for each person.
        persons = [
            {"name": "Eric", "house": m[Eric_pos].as_long(), "book": book_mapping[m[Eric_book].as_long()], "vac": vacation_mapping[m[Eric_vac].as_long()]},
            {"name": "Arnold", "house": m[Arnold_pos].as_long(), "book": book_mapping[m[Arnold_book].as_long()], "vac": vacation_mapping[m[Arnold_vac].as_long()]},
            {"name": "Peter", "house": m[Peter_pos].as_long(), "book": book_mapping[m[Peter_book].as_long()], "vac": vacation_mapping[m[Peter_vac].as_long()]}
        ]

        # Sort persons by the house number (1, 2, 3)
        persons = sorted(persons, key=lambda x: x["house"])

        # Build the rows for output as required.
        rows = []
        for p in persons:
            rows.append([str(p["house"]), p["name"], p["book"], p["vac"]])

        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()