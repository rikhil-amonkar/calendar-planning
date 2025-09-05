import itertools
import json

def solve():
    houses = [0, 1, 2]  # 0->House 1, 1->House 2, 2->House 3

    Names = ["Eric", "Peter", "Arnold"]
    Drinks = ["milk", "water", "tea"]
    Vacations = ["mountain", "city", "beach"]
    HouseStyles = ["colonial", "victorian", "ranch"]
    Animals = ["cat", "bird", "horse"]
    Birthdays = ["jan", "sept", "april"]

    # Fix: point perms to the permutations function (do not wrap in list)
    perms = itertools.permutations

    solutions = []

    for names in perms(Names):
        for drinks in perms(Drinks):
            for vacations in perms(Vacations):
                for styles in perms(HouseStyles):
                    for animals in perms(Animals):
                        for birthdays in perms(Birthdays):
                            # Helper to get position of a value in a category assignment
                            def pos(arr, val):
                                return arr.index(val)

                            # Clue 1: colonial left of milk
                            if not (pos(styles, "colonial") < pos(drinks, "milk")):
                                continue

                            # Clue 2: city directly left of victorian
                            if not (pos(vacations, "city") + 1 == pos(styles, "victorian")):
                                continue

                            # Clue 3: jan directly left of cat
                            if not (pos(birthdays, "jan") + 1 == pos(animals, "cat")):
                                continue

                            # Clue 4: water == mountain
                            if not (pos(drinks, "water") == pos(vacations, "mountain")):
                                continue

                            # Clue 5: horse == Peter
                            if not (pos(animals, "horse") == pos(names, "Peter")):
                                continue

                            # Clue 6: victorian right of beach
                            if not (pos(styles, "victorian") > pos(vacations, "beach")):
                                continue

                            # Clue 7: Peter == city
                            if not (pos(names, "Peter") == pos(vacations, "city")):
                                continue

                            # Clue 8: mountain == april
                            if not (pos(vacations, "mountain") == pos(birthdays, "april")):
                                continue

                            # Clue 9: Eric == water
                            if not (pos(names, "Eric") == pos(drinks, "water")):
                                continue

                            solutions.append((names, drinks, vacations, styles, animals, birthdays))

    if len(solutions) != 1:
        raise RuntimeError(f"Expected exactly one solution, found {len(solutions)}")

    names, drinks, vacations, styles, animals, birthdays = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
            "rows": [
                [str(i+1), names[i], drinks[i], vacations[i], styles[i], animals[i], birthdays[i]]
                for i in range(3)
            ]
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    solve()