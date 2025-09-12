import json
from z3 import *

def main():
    solver = Solver()

    # Define variables for each house (1, 2, 3)
    name_1, name_2, name_3 = Ints('name_1 name_2 name_3')
    animal_1, animal_2, animal_3 = Ints('animal_1 animal_2 animal_3')
    birthday_1, birthday_2, birthday_3 = Ints('birthday_1 birthday_2 birthday_3')
    hobby_1, hobby_2, hobby_3 = Ints('hobby_1 hobby_2 hobby_3')
    drink_1, drink_2, drink_3 = Ints('drink_1 drink_2 drink_3')
    haircolor_1, haircolor_2, haircolor_3 = Ints('haircolor_1 haircolor_2 haircolor_3')

    # Add constraints for uniqueness and domain
    solver.add(Distinct(name_1, name_2, name_3))
    solver.add(Distinct(animal_1, animal_2, animal_3))
    solver.add(Distinct(birthday_1, birthday_2, birthday_3))
    solver.add(Distinct(hobby_1, hobby_2, hobby_3))
    solver.add(Distinct(drink_1, drink_2, drink_3))
    solver.add(Distinct(haircolor_1, haircolor_2, haircolor_3))

    # Domain constraints: 0,1,2 for each attribute
    for var in [name_1, name_2, name_3]:
        solver.add(And(var >= 0, var <= 2))
    for var in [animal_1, animal_2, animal_3]:
        solver.add(And(var >= 0, var <= 2))
    for var in [birthday_1, birthday_2, birthday_3]:
        solver.add(And(var >= 0, var <= 2))
    for var in [hobby_1, hobby_2, hobby_3]:
        solver.add(And(var >= 0, var <= 2))
    for var in [drink_1, drink_2, drink_3]:
        solver.add(And(var >= 0, var <= 2))
    for var in [haircolor_1, haircolor_2, haircolor_3]:
        solver.add(And(var >= 0, var <= 2))

    # Clue 1: Brown hair (1) → cooking (1)
    solver.add(Implies(haircolor_1 == 1, hobby_1 == 1))
    solver.add(Implies(haircolor_2 == 1, hobby_2 == 1))
    solver.add(Implies(haircolor_3 == 1, hobby_3 == 1))

    # Clue 2: April (2) is in third house
    solver.add(birthday_3 == 2)

    # Clue 3: Eric (2) not in first house
    solver.add(name_1 != 2)

    # Clue 4: Cat (2) in second house
    solver.add(animal_2 == 2)

    # Clue 5: Blonde (2) left of milk (0)
    solver.add(Or(
        And(haircolor_1 == 2, Or(drink_2 == 0, drink_3 == 0)),
        And(haircolor_2 == 2, drink_3 == 0)
    ))

    # Clue 6: Gardening (2) is milk (0)
    for i in range(3):
        solver.add((hobby_1 + hobby_2 + hobby_3)[i] == 2 == (drink_1 + drink_2 + drink_3)[i] == 0)

    # Clue 7: Cat lover (animal=2) has brown hair (1). Since animal_2 is 2, haircolor_2 must be 1
    solver.add(haircolor_2 == 1)

    # Clue 8: Arnold (0) is bird keeper (0)
    for i in range(3):
        solver.add(Implies(names_list[i] == 0, animals_list[i] == 0))

    # Clue 9: Water (1) → photography (0)
    for i in range(3):
        solver.add(Implies(drinks_list[i] == 1, hobbies_list[i] == 0))

    # Clue 10: Sept (1) directly left of Arnold
    solver.add(Or(
        And(birthday_1 == 1, name_2 == 0),
        And(birthday_2 == 1, name_3 == 0)
    ))

    if solver.check() == sat:
        model = solver.model()

        # Prepare the solution
        names_list = [name_1, name_2, name_3]
        animals_list = [animal_1, animal_2, animal_3]
        birthdays_list = [birthday_1, birthday_2, birthday_3]
        hobbies_list = [hobby_1, hobby_2, hobby_3]
        drinks_list = [drink_1, drink_2, drink_3]
        haircolors_list = [haircolor_1, haircolor_2, haircolor_3]

        rows = []
        for i in range(3):
            house_num = str(i + 1)
            name_val = model[names_list[i]].as_long()
            animal_val = model[animals_list[i]].as_long()
            birthday_val = model[birthdays_list[i]].as_long()
            hobby_val = model[hobbies_list[i]].as_long()
            drink_val = model[drinks_list[i]].as_long()
            haircolor_val = model[haircolors_list[i]].as_long()

            name = ["Arnold", "Peter", "Eric"][name_val]
            animal = ["bird", "horse", "cat"][animal_val]
            birthday = ["jan", "sept", "april"][birthday_val]
            hobby = ["photography", "cooking", "gardening"][hobby_val]
            drink = ["milk", "water", "tea"][drink_val]
            haircolor = ["black", "brown", "blonde"][haircolor_val]

            rows.append([house_num, name, animal, birthday, hobby, drink, haircolor])

        solution = {
            "solution": {
                "header": ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"],
                "rows": rows
            }
        }

        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()