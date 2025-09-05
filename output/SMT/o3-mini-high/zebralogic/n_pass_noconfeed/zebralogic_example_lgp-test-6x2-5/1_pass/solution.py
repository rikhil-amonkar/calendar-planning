from z3 import Solver, Int, And, Distinct, sat
import json

def solve_puzzle():
    s = Solver()

    # Define persons and vacation types
    persons = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]

    # Create an integer variable for the house number (1-6) of each person.
    person_house = {p: Int(f"house_{p}") for p in persons}
    # Create an integer variable for the house number (1-6) of each vacation type.
    vac_house = {v: Int(f"house_{v}") for v in vacations}

    # Domain constraints: each value must be between 1 and 6.
    for p in persons:
        s.add(And(person_house[p] >= 1, person_house[p] <= 6))
    for v in vacations:
        s.add(And(vac_house[v] >= 1, vac_house[v] <= 6))

    # All persons and all vacations are in distinct houses.
    s.add(Distinct(list(person_house.values())))
    s.add(Distinct(list(vac_house.values())))

    # Clue 3: Eric is in the second house.
    s.add(person_house["Eric"] == 2)

    # Clue 2: Eric is somewhere to the right of Alice. (Meaning Alice's house number < Eric's house number)
    s.add(person_house["Eric"] > person_house["Alice"])

    # Clue 4: The person who goes on cultural tours is in the third house.
    s.add(vac_house["cultural"] == 3)

    # Clue 1: The person who goes on cultural tours is somewhere to the left of the person who loves beach vacations.
    s.add(vac_house["cultural"] < vac_house["beach"])

    # Clue 7: The person who goes on cultural tours is Peter.
    s.add(person_house["Peter"] == vac_house["cultural"])

    # Clue 9: The person who prefers city breaks is in the fourth house.
    s.add(vac_house["city"] == 4)

    # Clue 6: The person who enjoys camping trips is not in the first house.
    s.add(vac_house["camping"] != 1)

    # Clue 8: The person who likes going on cruises is Bob.
    s.add(person_house["Bob"] == vac_house["cruise"])

    # Clue 5: Bob is directly left of Arnold.
    s.add(person_house["Bob"] + 1 == person_house["Arnold"])

    # Solve the puzzle.
    if s.check() == sat:
        m = s.model()

        # Invert the person mapping: house number -> person.
        house_to_person = {}
        for p in persons:
            house_num = m.evaluate(person_house[p]).as_long()
            house_to_person[house_num] = p

        # Invert the vacation mapping: house number -> vacation.
        house_to_vacation = {}
        for v in vacations:
            house_num = m.evaluate(vac_house[v]).as_long()
            house_to_vacation[house_num] = v

        # Build the solution rows in the order of house numbers 1 to 6.
        rows = []
        for house in range(1, 7):
            row = [str(house), house_to_person[house], house_to_vacation[house]]
            rows.append(row)

        result = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
        return result
    else:
        return {"solution": None}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution))