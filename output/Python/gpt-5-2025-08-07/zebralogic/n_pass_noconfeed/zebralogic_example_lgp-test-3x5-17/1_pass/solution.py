import json
from itertools import permutations

def solve_puzzle():
    # Houses indexed 0..2 correspond to "1", "2", "3"
    houses = [0, 1, 2]

    # Attributes
    Names = ['Eric', 'Arnold', 'Peter']
    PhoneModels = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    Heights = ['very short', 'average', 'short']
    HouseStyles = ['colonial', 'ranch', 'victorian']
    CarModels = ['tesla model 3', 'toyota camry', 'ford f150']

    solution_rows = None

    for phone_perm in permutations(PhoneModels):
        # Clue 5: iPhone 13 is directly left of Google Pixel 6
        if phone_perm.index('iphone 13') + 1 != phone_perm.index('google pixel 6'):
            continue

        for height_perm in permutations(Heights):
            # Clue 9: Average height is in the first house
            if height_perm[0] != 'average':
                continue
            # Clue 4: Short is directly left of Samsung Galaxy S21
            if height_perm.index('short') + 1 != phone_perm.index('samsung galaxy s21'):
                continue

            for style_perm in permutations(HouseStyles):
                # Clue 2: Colonial is in the second house
                if style_perm[1] != 'colonial':
                    continue
                # Clue 6: Colonial is to the right of Ranch
                if style_perm.index('colonial') <= style_perm.index('ranch'):
                    continue

                for name_perm in permutations(Names):
                    # Clue 7: Arnold is in the second house
                    if name_perm[1] != 'Arnold':
                        continue
                    # Clue 1: Peter is to the right of Eric
                    if name_perm.index('Peter') <= name_perm.index('Eric'):
                        continue

                    for car_perm in permutations(CarModels):
                        # Clue 8: Ford F-150 is somewhere to the right of Toyota Camry
                        if car_perm.index('ford f150') <= car_perm.index('toyota camry'):
                            continue
                        # Clue 3: Tesla Model 3 owner is very short
                        if car_perm.index('tesla model 3') != height_perm.index('very short'):
                            continue

                        # Construct rows for the solution
                        rows = []
                        for i in houses:
                            rows.append([
                                str(i + 1),
                                name_perm[i],
                                phone_perm[i],
                                height_perm[i],
                                style_perm[i],
                                car_perm[i],
                            ])
                        solution_rows = rows
                        break
                    if solution_rows:
                        break
                if solution_rows:
                    break
            if solution_rows:
                break
        if solution_rows:
            break

    result = {
        "solution": {
            "header": ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"],
            "rows": solution_rows if solution_rows else []
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()