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
            # Clue 2: Toyota Camry is in the second house.
            if cars[1] != "toyota camry":
                continue
            for house_styles in itertools.permutations(house_styles_list):
                # Clue 6: The Toyota Camry is directly left of the colonial house.
                # Since Toyota is in house2, house3 must be colonial.
                if house_styles[2] != "colonial":
                    continue
                for pets in itertools.permutations(pets_list):
                    # Clue 1: The person with fish is in the first house.
                    if pets[0] != "fish":
                        continue
                    # Clue 7: Arnold is the person who has a cat.
                    arnold_index = names.index("Arnold")
                    if pets[arnold_index] != "cat":
                        continue
                    for occupations in itertools.permutations(occupations_list):
                        # Clue 9: The engineer is not in the third house.
                        if occupations[2] == "engineer":
                            continue
                        # Clue 11: The engineer owns the dog.
                        valid = True
                        for i in range(3):
                            if occupations[i] == "engineer" and pets[i] != "dog":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Clue 10: The Tesla Model 3 is somewhere to the left of the teacher.
                        tesla_index = cars.index("tesla model 3")
                        teacher_index = occupations.index("teacher")
                        if tesla_index >= teacher_index:
                            continue
                        # Clue 5: The person in a ranch-style home is somewhere to the left of Peter.
                        ranch_index = house_styles.index("ranch")
                        peter_index = names.index("Peter")
                        if not (ranch_index < peter_index):
                            continue
                        for vacations in itertools.permutations(vacations_list):
                            # Clue 3 & 4: The person who enjoys mountain retreats and city breaks
                            # are not in the second house. Thus, house2 vacation must be neither mountain nor city.
                            if vacations[1] in ["mountain", "city"]:
                                continue
                            # Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
                            eric_index = names.index("Eric")
                            mountain_index = vacations.index("mountain")
                            if eric_index >= mountain_index:
                                continue

                            # All constraints satisfied: build the solution.
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Car", "House style", "Pet", "Occupation", "Vacation"],
                                    "rows": [
                                        ["1", names[0], cars[0], house_styles[0], pets[0], occupations[0], vacations[0]],
                                        ["2", names[1], cars[1], house_styles[1], pets[1], occupations[1], vacations[1]],
                                        ["3", names[2], cars[2], house_styles[2], pets[2], occupations[2], vacations[2]]
                                    ]
                                }
                            }
                            print(json.dumps(solution, indent=2))
                            return

if __name__ == '__main__':
    main()