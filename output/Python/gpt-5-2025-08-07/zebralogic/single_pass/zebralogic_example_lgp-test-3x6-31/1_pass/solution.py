import json
import itertools

def solve_puzzle():
    houses = [0, 1, 2]  # indices for houses 1..3

    Names = ['Eric', 'Peter', 'Arnold']
    Drinks = ['milk', 'water', 'tea']
    Vacations = ['mountain', 'city', 'beach']
    Styles = ['colonial', 'victorian', 'ranch']
    Animals = ['cat', 'bird', 'horse']
    Birthdays = ['jan', 'sept', 'april']

    def idx(lst, value):
        return lst.index(value)

    def left_of(a, b):
        return a < b

    def directly_left_of(a, b):
        return a + 1 == b

    solutions = []

    for name_at in itertools.permutations(Names):
        # Clue 5: The person who keeps horses is Peter. (handled later with animals)
        # Clue 7: Peter is the person who prefers city breaks. (check when vacations assigned)
        # Clue 9: Eric is the one who only drinks water. (check when drinks assigned)

        for drink_at in itertools.permutations(Drinks):
            # Clue 9: Eric -> water
            if drink_at[idx(name_at, 'Eric')] != 'water':
                continue

            for vac_at in itertools.permutations(Vacations):
                # Clue 4: water == mountain
                if idx(drink_at, 'water') != idx(vac_at, 'mountain'):
                    continue
                # Clue 7: Peter == city
                if vac_at[idx(name_at, 'Peter')] != 'city':
                    continue

                for style_at in itertools.permutations(Styles):
                    # Clue 2: city directly left of Victorian
                    if not directly_left_of(idx(vac_at, 'city'), idx(style_at, 'victorian')):
                        continue
                    # Clue 6: Victorian right of beach
                    if not left_of(idx(vac_at, 'beach'), idx(style_at, 'victorian')):
                        continue
                    # Clue 1: colonial left of milk
                    if not left_of(idx(style_at, 'colonial'), idx(drink_at, 'milk')):
                        continue

                    for animal_at in itertools.permutations(Animals):
                        # Clue 5: Peter keeps horses
                        if animal_at[idx(name_at, 'Peter')] != 'horse':
                            continue

                        for bday_at in itertools.permutations(Birthdays):
                            # Clue 8: mountain == april
                            if idx(vac_at, 'mountain') != idx(bday_at, 'april'):
                                continue
                            # Clue 3: January directly left of cat lover
                            if not directly_left_of(idx(bday_at, 'jan'), idx(animal_at, 'cat')):
                                continue

                            # All constraints satisfied, collect solution
                            solution = []
                            for h in houses:
                                solution.append({
                                    "House": str(h + 1),
                                    "Name": name_at[h],
                                    "Drink": drink_at[h],
                                    "Vacation": vac_at[h],
                                    "HouseStyle": style_at[h],
                                    "Animal": animal_at[h],
                                    "Birthday": bday_at[h],
                                })
                            solutions.append(solution)

    # Expect exactly one solution
    if not solutions:
        raise RuntimeError("No solution found.")
    sol = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
            "rows": [
                [row["House"], row["Name"], row["Drink"], row["Vacation"], row["HouseStyle"], row["Animal"], row["Birthday"]]
                for row in sol
            ]
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))