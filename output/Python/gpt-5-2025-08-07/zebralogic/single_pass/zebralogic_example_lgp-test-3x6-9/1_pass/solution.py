import itertools
import json

def solve_puzzle():
    # Houses indexed 0..2 correspond to 1..3
    houses = [0, 1, 2]

    Names = ['Peter', 'Arnold', 'Eric']
    CarModels = ['toyota camry', 'ford f150', 'tesla model 3']
    HouseStyles = ['ranch', 'colonial', 'victorian']
    Pets = ['cat', 'dog', 'fish']
    Occupations = ['engineer', 'doctor', 'teacher']
    Vacations = ['city', 'mountain', 'beach']

    solutions = []

    for name_at in itertools.permutations(Names):
        # Clues involving names will be checked later with other attributes
        for car_at in itertools.permutations(CarModels):
            # 2. The person who owns a Toyota Camry is in the second house.
            if car_at[1] != 'toyota camry':
                continue

            for style_at in itertools.permutations(HouseStyles):
                # 6. The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
                # Since Camry is in house 2, Colonial must be in house 3.
                if style_at[2] != 'colonial':
                    continue
                if car_at.index('toyota camry') + 1 != style_at.index('colonial'):
                    continue

                for pet_at in itertools.permutations(Pets):
                    # 1. The person with an aquarium of fish is in the first house.
                    if pet_at[0] != 'fish':
                        continue
                    # 7. Arnold is the person who has a cat.
                    arnold_house = name_at.index('Arnold')
                    if pet_at[arnold_house] != 'cat':
                        continue

                    for occup_at in itertools.permutations(Occupations):
                        # 9. The person who is an engineer is not in the third house.
                        if occup_at[2] == 'engineer':
                            continue
                        # 11. The person who owns a dog is the person who is an engineer.
                        consistent = True
                        for h in houses:
                            if (pet_at[h] == 'dog') != (occup_at[h] == 'engineer'):
                                consistent = False
                                break
                        if not consistent:
                            continue

                        for vac_at in itertools.permutations(Vacations):
                            # 3. The person who enjoys mountain retreats is not in the second house.
                            if vac_at[1] == 'mountain':
                                continue
                            # 4. The person who prefers city breaks is not in the second house.
                            if vac_at[1] == 'city':
                                continue
                            # 8. Eric is somewhere to the left of the person who enjoys mountain retreats.
                            if name_at.index('Eric') >= vac_at.index('mountain'):
                                continue
                            # 10. The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
                            if car_at.index('tesla model 3') >= occup_at.index('teacher'):
                                continue
                            # 5. The person in a ranch-style home is somewhere to the left of Peter.
                            if style_at.index('ranch') >= name_at.index('Peter'):
                                continue

                            # All constraints satisfied; record solution
                            solutions.append((name_at, car_at, style_at, pet_at, occup_at, vac_at))

    if not solutions:
        raise RuntimeError("No solution found.")
    # If multiple solutions, choose the first; typically Zebra puzzles have a unique solution
    name_at, car_at, style_at, pet_at, occup_at, vac_at = solutions[0]

    result = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": []
        }
    }

    for i in range(3):  # houses 0..2 => 1..3
        row = [
            str(i + 1),
            name_at[i],
            car_at[i],
            style_at[i],
            pet_at[i],
            occup_at[i],
            vac_at[i]
        ]
        result["solution"]["rows"].append(row)

    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))