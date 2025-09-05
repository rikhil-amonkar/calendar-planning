#!/usr/bin/env python3
import json
from z3 import *

def main():
    solver = Solver()
    houses = 3

    # Define variables for each attribute in each house (0-indexed houses)
    names   = [Int(f"name_{i}") for i in range(houses)]
    cigars  = [Int(f"cigar_{i}") for i in range(houses)]
    animals = [Int(f"animal_{i}") for i in range(houses)]
    children = [Int(f"child_{i}") for i in range(houses)]
    books   = [Int(f"book_{i}") for i in range(houses)]
    phones  = [Int(f"phone_{i}") for i in range(houses)]

    # All variables must be within {0,1,2}
    all_vars = names + cigars + animals + children + books + phones
    for var in all_vars:
        solver.add(And(var >= 0, var < houses))

    # Each attribute must be assigned uniquely across houses.
    solver.add(Distinct(names))
    solver.add(Distinct(cigars))
    solver.add(Distinct(animals))
    solver.add(Distinct(children))
    solver.add(Distinct(books))
    solver.add(Distinct(phones))

    # Mappings:
    # Names: 0: Arnold, 1: Eric, 2: Peter
    # Cigars: 0: pall mall, 1: blue master, 2: prince
    # Animals: 0: horse, 1: cat, 2: bird
    # Children: 0: Bella, 1: Fred, 2: Meredith
    # Book Genres: 0: science fiction, 1: romance, 2: mystery
    # Phones: 0: google pixel 6, 1: iphone 13, 2: samsung galaxy s21

    # Clue 1: The person who loves mystery books has a child named Fred.
    for i in range(houses):
        solver.add(Implies(books[i] == 2, children[i] == 1))

    # Clue 2: The cat lover is Eric.
    # Enforce the equivalence: a house's resident is Eric if and only if that house's animal is a cat.
    for i in range(houses):
        solver.add(If(names[i] == 1, animals[i] == 1, True))
        solver.add(If(animals[i] == 1, names[i] == 1, True))

    # Clue 3: The person partial to Pall Mall is in the second house.
    solver.add(cigars[1] == 0)

    # Clue 4: The person who keeps horses has a child named Meredith.
    for i in range(houses):
        solver.add(Implies(animals[i] == 0, children[i] == 2))

    # Clue 5: The person whose child is named Bella smokes Prince.
    for i in range(houses):
        solver.add(Implies(children[i] == 0, cigars[i] == 2))

    # Clue 6: The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
    # Either house0 has iphone13 and house1 has samsung galaxy s21 or house1 has iphone13 and house2 has samsung galaxy s21.
    solver.add(Or(And(phones[0] == 1, phones[1] == 2),
                  And(phones[1] == 1, phones[2] == 2)))

    # Clue 7: The person whose child is named Fred is directly left of Arnold.
    # That means either house0's child is Fred and house1's resident is Arnold,
    # or house1's child is Fred and house2's resident is Arnold.
    solver.add(Or(And(children[0] == 1, names[1] == 0),
                  And(children[1] == 1, names[2] == 0)))

    # Clue 8: Peter is somewhere to the left of Eric.
    # Compute the position (index) where each occurs.
    posPeter = Sum([If(names[i] == 2, i, 0) for i in range(houses)])
    posEric  = Sum([If(names[i] == 1, i, 0) for i in range(houses)])
    solver.add(posPeter < posEric)

    # Clue 9: The person who loves science fiction books uses a Samsung Galaxy S21.
    # Enforce the equivalence in each house.
    for i in range(houses):
        solver.add(Implies(books[i] == 0, phones[i] == 2))
        solver.add(Implies(phones[i] == 2, books[i] == 0))

    # Clue 10: The person who loves science fiction books is in the third house.
    solver.add(books[2] == 0)

    # Clue 11: The person who loves mystery books is not in the second house.
    solver.add(books[1] != 2)

    # Solve the puzzle.
    if solver.check() == sat:
        model = solver.model()

        # Mapping dictionaries for output.
        names_map   = {0: "Arnold", 1: "Eric", 2: "Peter"}
        cigars_map  = {0: "pall mall", 1: "blue master", 2: "prince"}
        animals_map = {0: "horse", 1: "cat", 2: "bird"}
        children_map = {0: "Bella", 1: "Fred", 2: "Meredith"}
        books_map   = {0: "science fiction", 1: "romance", 2: "mystery"}
        phones_map  = {0: "google pixel 6", 1: "iphone 13", 2: "samsung galaxy s21"}

        header = ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"]
        rows = []
        for i in range(houses):
            house_no = str(i + 1)
            name_val = names_map[model.evaluate(names[i]).as_long()]
            cigar_val = cigars_map[model.evaluate(cigars[i]).as_long()]
            animal_val = animals_map[model.evaluate(animals[i]).as_long()]
            child_val = children_map[model.evaluate(children[i]).as_long()]
            book_val = books_map[model.evaluate(books[i]).as_long()]
            phone_val = phones_map[model.evaluate(phones[i]).as_long()]
            rows.append([house_no, name_val, cigar_val, animal_val, child_val, book_val, phone_val])

        solution = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()