from z3 import Solver, Int, And, Distinct, Implies, If
import json

def main():
    solver = Solver()
    n = 3  # three houses; indices 0,1,2 correspond to houses 1,2,3

    # Create one variable per house for each attribute.
    names   = [Int(f"name_{i}") for i in range(n)]
    cigars  = [Int(f"cigar_{i}") for i in range(n)]
    animals = [Int(f"animal_{i}") for i in range(n)]
    children = [Int(f"child_{i}") for i in range(n)]
    books    = [Int(f"book_{i}") for i in range(n)]
    phones   = [Int(f"phone_{i}") for i in range(n)]

    # All values are in the domain {0, 1, 2}.
    all_vars = names + cigars + animals + children + books + phones
    for var in all_vars:
        solver.add(And(var >= 0, var < n))

    # Each category gives a permutation of the 3 possibilities.
    solver.add(Distinct(names))
    solver.add(Distinct(cigars))
    solver.add(Distinct(animals))
    solver.add(Distinct(children))
    solver.add(Distinct(books))
    solver.add(Distinct(phones))

    # We will use the following mappings for our integer encodings:
    #
    # Names:      Arnold=0, Eric=1, Peter=2
    # Cigars:     blue master=0, pall mall=1, prince=2
    # Animals:    bird=0, horse=1, cat=2
    # Children:   Fred=0, Meredith=1, Bella=2
    # Books:      mystery=0, romance=1, science fiction=2
    # Phones:     google pixel 6=0, iphone 13=1, samsung galaxy s21=2

    # Clue 1. "The person who loves mystery books is the person's child is named Fred."
    #         -> If a house's book genre is mystery (0) then its child is Fred (0).
    for i in range(n):
        solver.add(Implies(books[i] == 0, children[i] == 0))

    # Clue 2. "The cat lover is Eric."
    #         -> In any house, if the animal is cat (2) then the name is Eric (1).
    for i in range(n):
        solver.add(Implies(animals[i] == 2, names[i] == 1))

    # Clue 3. "The person partial to Pall Mall is in the second house."
    #         -> House2 (index 1) has cigar = pall mall (1).
    solver.add(cigars[1] == 1)

    # Clue 4. "The person who keeps horses is the person's child is named Meredith."
    #         -> If a house has animal horse (1) then its child is Meredith (1).
    for i in range(n):
        solver.add(Implies(animals[i] == 1, children[i] == 1))

    # Clue 5. "The person's child is named Bella is the Prince smoker."
    #         -> If a house's child is Bella (2) then its cigar is prince (2).
    for i in range(n):
        solver.add(Implies(children[i] == 2, cigars[i] == 2))

    # Clue 6. "The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21."
    #         -> If a house uses iphone 13 (1) then the house immediately to its right uses samsung galaxy s21 (2).
    #   Because the phones are all different, we can “find” the positions by checking the first two houses.
    pos_iphone = If(phones[0] == 1, 0, If(phones[1] == 1, 1, 2))
    pos_samsung = If(phones[0] == 2, 0, If(phones[1] == 2, 1, 2))
    solver.add(pos_samsung == pos_iphone + 1)

    # Clue 7. "The person's child is named Fred is directly left of Arnold."
    #         -> The house where the child is Fred (0) is immediately to the left of the house whose name is Arnold (0).
    pos_fred = If(children[0] == 0, 0, If(children[1] == 0, 1, 2))
    pos_arnold = If(names[0] == 0, 0, If(names[1] == 0, 1, 2))
    solver.add(pos_arnold == pos_fred + 1)

    # Clue 8. "Peter is somewhere to the left of Eric."
    #         -> The house with Peter (2) must have a lower index than the house with Eric (1).
    pos_peter = If(names[0] == 2, 0, If(names[1] == 2, 1, 2))
    pos_eric = If(names[0] == 1, 0, If(names[1] == 1, 1, 2))
    solver.add(pos_peter < pos_eric)

    # Clue 9. "The person who loves science fiction books is the person who uses a Samsung Galaxy S21."
    #         -> If a house’s book genre is science fiction (2) then its phone is samsung galaxy s21 (2).
    for i in range(n):
        solver.add(Implies(books[i] == 2, phones[i] == 2))

    # Clue 10. "The person who loves science fiction books is in the third house."
    #         -> House3 (index 2) has book = science fiction (2).
    solver.add(books[2] == 2)

    # Clue 11. "The person who loves mystery books is not in the second house."
    #         -> House2 (index 1) cannot have book = mystery (0).
    solver.add(books[1] != 0)

    # Solve the model.
    if solver.check() == 'sat' or solver.check():
        mod = solver.model()

        # Define our mapping dictionaries to turn numbers back to strings.
        names_map = {0: "Arnold", 1: "Eric", 2: "Peter"}
        cigars_map = {0: "blue master", 1: "pall mall", 2: "prince"}
        animals_map = {0: "bird", 1: "horse", 2: "cat"}
        children_map = {0: "Fred", 1: "Meredith", 2: "Bella"}
        books_map = {0: "mystery", 1: "romance", 2: "science fiction"}
        phones_map = {0: "google pixel 6", 1: "iphone 13", 2: "samsung galaxy s21"}

        solution_rows = []
        for i in range(n):
            house_number = str(i + 1)
            name_val = names_map[mod.evaluate(names[i]).as_long()]
            cigar_val = cigars_map[mod.evaluate(cigars[i]).as_long()]
            animal_val = animals_map[mod.evaluate(animals[i]).as_long()]
            child_val = children_map[mod.evaluate(children[i]).as_long()]
            book_val = books_map[mod.evaluate(books[i]).as_long()]
            phone_val = phones_map[mod.evaluate(phones[i]).as_long()]
            solution_rows.append([house_number, name_val, cigar_val, animal_val, child_val, book_val, phone_val])

        result = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()