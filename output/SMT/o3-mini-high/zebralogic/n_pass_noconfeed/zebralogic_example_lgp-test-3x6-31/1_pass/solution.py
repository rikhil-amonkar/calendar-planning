from z3 import *
import json

def main():
    # There are 3 houses: indices 0, 1, 2 (representing houses 1,2,3 from left to right)
    n = 3

    # Create Z3 integer variables for each house's attributes
    names = [Int(f"name_{i}") for i in range(n)]
    drinks = [Int(f"drink_{i}") for i in range(n)]
    vacations = [Int(f"vacation_{i}") for i in range(n)]
    styles = [Int(f"style_{i}") for i in range(n)]
    animals = [Int(f"animal_{i}") for i in range(n)]
    birthdays = [Int(f"birthday_{i}") for i in range(n)]

    s = Solver()

    # Domain for each attribute: values 0,1,2
    for i in range(n):
        s.add(names[i] >= 0, names[i] < 3)
        s.add(drinks[i] >= 0, drinks[i] < 3)
        s.add(vacations[i] >= 0, vacations[i] < 3)
        s.add(styles[i] >= 0, styles[i] < 3)
        s.add(animals[i] >= 0, animals[i] < 3)
        s.add(birthdays[i] >= 0, birthdays[i] < 3)

    # All different constraints for each category
    s.add(Distinct(names))
    s.add(Distinct(drinks))
    s.add(Distinct(vacations))
    s.add(Distinct(styles))
    s.add(Distinct(animals))
    s.add(Distinct(birthdays))

    # Mappings for interpretation:
    # Name: 0 -> Eric, 1 -> Peter, 2 -> Arnold
    # Drink: 0 -> water, 1 -> milk, 2 -> tea
    # Vacation: 0 -> mountain, 1 -> city, 2 -> beach
    # HouseStyle: 0 -> colonial, 1 -> victorian, 2 -> ranch
    # Animal: 0 -> cat, 1 -> bird, 2 -> horse
    # Birthday: 0 -> jan, 1 -> sept, 2 -> april

    # Clue 4: The one who only drinks water is the person who enjoys mountain retreats.
    # <==> For each house: drink==water (0) if and only if vacation==mountain (0)
    for i in range(n):
        s.add(Implies(drinks[i] == 0, vacations[i] == 0))
        s.add(Implies(vacations[i] == 0, drinks[i] == 0))

    # Clue 8: The person who enjoys mountain retreats is the person whose birthday is in April.
    # <==> For each house: vacation==mountain (0) if and only if birthday==april (2)
    for i in range(n):
        s.add(Implies(vacations[i] == 0, birthdays[i] == 2))
        s.add(Implies(birthdays[i] == 2, vacations[i] == 0))

    # Clue 7: Peter is the person who prefers city breaks.
    # <==> For each house: name==Peter (1) if and only if vacation==city (1)
    for i in range(n):
        s.add(Implies(names[i] == 1, vacations[i] == 1))
        s.add(Implies(vacations[i] == 1, names[i] == 1))

    # Clue 5: The person who keeps horses is Peter.
    # <==> For each house: animal==horse (2) if and only if name==Peter (1)
    for i in range(n):
        s.add(Implies(animals[i] == 2, names[i] == 1))
        s.add(Implies(names[i] == 1, animals[i] == 2))

    # Clue 9: Eric is the one who only drinks water.
    # <==> For each house: name==Eric (0) if and only if drink==water (0)
    for i in range(n):
        s.add(Implies(names[i] == 0, drinks[i] == 0))
        s.add(Implies(drinks[i] == 0, names[i] == 0))

    # Clue 1: The person living in a colonial-style house is somewhere to the left of the person who likes milk.
    # Colonial house = 0, milk = 1; so possible pairs: (house0,house1), (house0,house2), (house1,house2)
    s.add(Or(
        And(styles[0] == 0, Or(drinks[1] == 1, drinks[2] == 1)),
        And(styles[1] == 0, drinks[2] == 1)
    ))

    # Clue 2: The person who prefers city breaks is directly left of the person residing in a Victorian house.
    # City = 1, Victorian = 1 and "directly left" means adjacent
    s.add(Or(
        And(vacations[0] == 1, styles[1] == 1),
        And(vacations[1] == 1, styles[2] == 1)
    ))

    # Clue 3: The person whose birthday is in January is directly left of the cat lover.
    # January = 0, cat = 0
    s.add(Or(
        And(birthdays[0] == 0, animals[1] == 0),
        And(birthdays[1] == 0, animals[2] == 0)
    ))

    # Clue 6: The person residing in a Victorian house is somewhere to the right of the person who loves beach vacations.
    # Beach = 2, Victorian = 1; not necessarily adjacent, just later.
    s.add(Or(
        And(vacations[0] == 2, Or(styles[1] == 1, styles[2] == 1)),
        And(vacations[1] == 2, styles[2] == 1)
    ))

    # Check solver
    if s.check() == sat:
        m = s.model()

        # Prepare mapping dictionaries for output
        name_map = {0: "Eric", 1: "Peter", 2: "Arnold"}
        drink_map = {0: "water", 1: "milk", 2: "tea"}
        vacation_map = {0: "mountain", 1: "city", 2: "beach"}
        style_map = {0: "colonial", 1: "victorian", 2: "ranch"}
        animal_map = {0: "cat", 1: "bird", 2: "horse"}
        birthday_map = {0: "jan", 1: "sept", 2: "april"}

        rows = []
        for i in range(n):
            house_number = str(i + 1)
            name_val = m[names[i]].as_long()
            drink_val = m[drinks[i]].as_long()
            vacation_val = m[vacations[i]].as_long()
            style_val = m[styles[i]].as_long()
            animal_val = m[animals[i]].as_long()
            birthday_val = m[birthdays[i]].as_long()

            row = [
                house_number,
                name_map[name_val],
                drink_map[drink_val],
                vacation_map[vacation_val],
                style_map[style_val],
                animal_map[animal_val],
                birthday_map[birthday_val]
            ]
            rows.append(row)

        solution = {
            "solution": {
                "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()