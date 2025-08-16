#!/usr/bin/env python3
import itertools
import json

def main():
    names_list = ["Peter", "Arnold", "Eric"]
    cars_list = ["toyota camry", "ford f150", "tesla model 3"]
    house_styles_list = ["ranch", "colonial", "victorian"]
    pets_list = ["cat", "dog", "fish"]
    occupations_list = ["engineer", "doctor", "teacher"]
    vacations_list = ["city", "mountain", "beach"]

    for names in itertools.permutations(names_list):
        for cars in itertools.permutations(cars_list):
            # Clue 2: The person who owns a Toyota Camry is in the second house.
            if cars[1] != "toyota camry":
                continue
            for hs in itertools.permutations(house_styles_list):
                # Clue 6: The Toyota Camry is directly left of the colonial house.
                # Since Toyota Camry is in the second house, the third house must be colonial.
                if hs[2] != "colonial":
                    continue
                for pets in itertools.permutations(pets_list):
                    # Clue 1: The person with fish is in the first house.
                    if pets[0] != "fish":
                        continue
                    for occ in itertools.permutations(occupations_list):
                        # Clue 9: The engineer is not in the third house.
                        if occ[2] == "engineer":
                            continue
                        # Clue 11: The person who owns a dog is the person who is an engineer.
                        valid_engineer_dog = True
                        for i in range(3):
                            if occ[i] == "engineer" and pets[i] != "dog":
                                valid_engineer_dog = False
                                break
                            if pets[i] == "dog" and occ[i] != "engineer":
                                valid_engineer_dog = False
                                break
                        if not valid_engineer_dog:
                            continue
                        for vac in itertools.permutations(vacations_list):
                            # Clue 3 & 4: second house's vacation is neither mountain nor city.
                            # Therefore, second house's vacation must be beach.
                            if vac[1] != "beach":
                                continue

                            valid = True

                            # Clue 5: The person in a ranch-style home is somewhere to the left of Peter.
                            try:
                                ranch_index = hs.index("ranch")
                                peter_index = names.index("Peter")
                            except ValueError:
                                valid = False
                            if not (ranch_index < peter_index):
                                valid = False

                            # Clue 7: Arnold has a cat.
                            for i in range(3):
                                if names[i] == "Arnold" and pets[i] != "cat":
                                    valid = False
                                    break

                            # Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
                            try:
                                eric_index = names.index("Eric")
                                mountain_index = vac.index("mountain")
                            except ValueError:
                                valid = False
                            if not (eric_index < mountain_index):
                                valid = False

                            # Clue 10: The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
                            try:
                                tesla_index = cars.index("tesla model 3")
                                teacher_index = occ.index("teacher")
                            except ValueError:
                                valid = False
                            if not (tesla_index < teacher_index):
                                valid = False

                            if valid:
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                                        "rows": [
                                            ["1", names[0], cars[0], hs[0], pets[0], occ[0], vac[0]],
                                            ["2", names[1], cars[1], hs[1], pets[1], occ[1], vac[1]],
                                            ["3", names[2], cars[2], hs[2], pets[2], occ[2], vac[2]]
                                        ]
                                    }
                                }
                                print(json.dumps(solution))
                                return

if __name__ == "__main__":
    main()