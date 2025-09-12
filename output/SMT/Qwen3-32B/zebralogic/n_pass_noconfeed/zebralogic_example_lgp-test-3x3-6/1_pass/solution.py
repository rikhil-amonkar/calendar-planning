import json
from z3 import *

def main():
    solver = Solver()

    # Define variables for each house (1, 2, 3)
    name_1, name_2, name_3 = Ints('name_1 name_2 name_3')
    name_vars = [name_1, name_2, name_3]

    book_1, book_2, book_3 = Ints('book_1 book_2 book_3')
    book_vars = [book_1, book_2, book_3]

    vac_1, vac_2, vac_3 = Ints('vac_1 vac_2 vac_3')
    vac_vars = [vac_1, vac_2, vac_3]

    p_house, b_house, m_house = Ints('p_house b_house m_house')

    # All variables are between 0 and 2
    for var in name_vars + book_vars + vac_vars:
        solver.add(And(0 <= var, var <= 2))

    # Each category has distinct values
    solver.add(Distinct(name_1, name_2, name_3))
    solver.add(Distinct(book_1, book_2, book_3))
    solver.add(Distinct(vac_1, vac_2, vac_3))

    # Clue 1: Eric (0) directly left of Arnold (1)
    clue1 = Or(
        And(name_1 == 0, name_2 == 1),
        And(name_2 == 0, name_3 == 1)
    )
    solver.add(clue1)

    # Constraints for p_house (Peter's house)
    solver.add(And(1 <= p_house, p_house <= 3))
    solver.add((name_1 == 2) == (p_house == 1))
    solver.add((name_2 == 2) == (p_house == 2))
    solver.add((name_3 == 2) == (p_house == 3))

    # Constraints for b_house (beach vacation)
    solver.add(And(1 <= b_house, b_house <= 3))
    solver.add((vac_1 == 1) == (b_house == 1))
    solver.add((vac_2 == 1) == (b_house == 2))
    solver.add((vac_3 == 1) == (b_house == 3))

    # Constraints for m_house (mystery book)
    solver.add(And(1 <= m_house, m_house <= 3))
    solver.add((book_1 == 0) == (m_house == 1))
    solver.add((book_2 == 0) == (m_house == 2))
    solver.add((book_3 == 0) == (m_house == 3))

    # Clue 2: Peter is to the right of beach
    solver.add(p_house > b_house)

    # Clue 3: Peter's vacation is city (2)
    clue3 = Or(
        And(p_house == 1, vac_1 == 2),
        And(p_house == 2, vac_2 == 2),
        And(p_house == 3, vac_3 == 2)
    )
    solver.add(clue3)

    # Clue 4: mystery is left of beach
    solver.add(m_house < b_house)

    # Clue 5: beach vacation's book is science fiction (1)
    clue5 = Or(
        And(b_house == 1, book_1 == 1),
        And(b_house == 2, book_2 == 1),
        And(b_house == 3, book_3 == 1)
    )
    solver.add(clue5)

    if solver.check() == sat:
        model = solver.model()
        rows = []
        for i in [1, 2, 3]:
            idx = i - 1
            name_val = model[name_vars[idx]].as_long()
            book_val = model[book_vars[idx]].as_long()
            vac_val = model[vac_vars[idx]].as_long()
            name_str = {0: 'Eric', 1: 'Arnold', 2: 'Peter'}[name_val]
            book_str = {0: 'mystery', 1: 'science fiction', 2: 'romance'}[book_val]
            vac_str = {0: 'mountain', 1: 'beach', 2: 'city'}[vac_val]
            rows.append([str(i), name_str, book_str, vac_str])
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