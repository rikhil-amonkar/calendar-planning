import json
import itertools

def idx(lst, value):
    return lst.index(value)

def solve_puzzle():
    houses = [0, 1, 2]  # 0->House 1, 1->House 2, 2->House 3

    Names = ['Eric', 'Arnold', 'Peter']
    PhoneModels = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    Heights = ['very short', 'average', 'short']
    HouseStyles = ['colonial', 'ranch', 'victorian']
    CarModels = ['tesla model 3', 'toyota camry', 'ford f150']

    solutions = []

    for names in itertools.permutations(Names):
        # Clue 7: Arnold is in the second house.
        if names[1] != 'Arnold':
            continue
        # Clue 1: Peter is somewhere to the right of Eric.
        if idx(names, 'Peter') <= idx(names, 'Eric'):
            continue

        for heights in itertools.permutations(Heights):
            # Clue 9: The person who has an average height is in the first house.
            if heights[0] != 'average':
                continue

            for phones in itertools.permutations(PhoneModels):
                # Clue 5: iPhone 13 directly left of Google Pixel 6.
                if not (idx(phones, 'iphone 13') + 1 == idx(phones, 'google pixel 6')):
                    continue
                # Clue 4: short directly left of Samsung Galaxy S21.
                if not (idx(heights, 'short') + 1 == idx(phones, 'samsung galaxy s21')):
                    continue

                # House styles fixed by clues 2 and 6
                # Clue 2: colonial is in the second house.
                # Clue 6: colonial is somewhere to the right of ranch -> ranch must be first.
                styles = [None, None, None]
                styles[1] = 'colonial'
                styles[0] = 'ranch'
                styles[2] = 'victorian'

                for cars in itertools.permutations(CarModels):
                    # Clue 8: Ford F-150 to the right of Toyota Camry.
                    if not (idx(cars, 'ford f150') > idx(cars, 'toyota camry')):
                        continue
                    # Clue 3: Tesla Model 3 owner is very short.
                    if idx(cars, 'tesla model 3') != idx(heights, 'very short'):
                        continue

                    # All constraints satisfied; record solution
                    solution_rows = []
                    for h in houses:
                        solution_rows.append([
                            str(h + 1),
                            names[h],
                            phones[h],
                            heights[h],
                            styles[h],
                            cars[h]
                        ])
                    solutions.append(solution_rows)

    if not solutions:
        raise ValueError("No solution found.")
    # Expect a unique solution; take the first.
    final_rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
            "rows": final_rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))