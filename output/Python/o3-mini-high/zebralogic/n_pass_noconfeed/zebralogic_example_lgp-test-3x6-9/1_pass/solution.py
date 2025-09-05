import itertools
import json

def solve():
    # Fixed domains based on the puzzle deductions:
    # Houses are numbered 1, 2, 3 (from left to right).
    # Attributes: Name, CarModel, HouseStyle, Pet, Occupation, Vacation.
    names = ["Peter", "Arnold", "Eric"]
    # Cars: "toyota camry", "tesla model 3", "ford f150"
    # Based on clues: The Toyota Camry is in the second house.
    car_options = ["tesla model 3", "ford f150"]  # for houses 1 and 3. House 2 is fixed.
    # HouseStyles: "ranch", "colonial", "victorian"
    # Clue: House 3 is colonial (from the rule that the Toyota Camry is directly left of the colonial house)
    house_style_options = ["ranch", "victorian"]  # for houses 1 and 2. House 3 fixed.
    # Pets: "cat", "dog", "fish"
    # Clue: House 1 has fish.
    pet_options = ["cat", "dog"]  # for houses 2 and 3; House 1 fixed.
    # Occupations: "engineer", "doctor", "teacher"
    occupations = ["engineer", "doctor", "teacher"]
    # Vacations: "city", "mountain", "beach"
    # Clues: House 2 is neither mountain (clue 3) nor city (clue 4),
    # and by elimination and clue 8 (Eric is left of the mountain vacation) house 1 = city, house 2 = beach, house 3 = mountain.
    vacations = {1: "city", 2: "beach", 3: "mountain"}
    
    solutions = []
    # Iterate over possible assignments for houses 1,2,3.
    # House number -> attributes will be stored in dictionaries with key 1, 2, 3.
    for name_perm in itertools.permutations(names):
        house_names = {1: name_perm[0], 2: name_perm[1], 3: name_perm[2]}
        # Clue 7: Arnold has a cat.
        # So if Arnold is in a house with a fixed pet that is not cat, then reject.
        # House 1 already has fish, so Arnold cannot be in house 1.
        if house_names[1] == "Arnold":
            continue
        # Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
        # Since mountain vacation is fixed to house 3, Eric cannot be in house 3.
        if house_names[3] == "Eric":
            continue

        # Car assignments: House 2 is fixed to "toyota camry".
        for car_perm in itertools.permutations(car_options):
            house_cars = {1: car_perm[0], 2: "toyota camry", 3: car_perm[1]}

            # HouseStyle assignments: House 3 is fixed to "colonial"
            for hs_perm in itertools.permutations(house_style_options):
                house_styles = {1: hs_perm[0], 2: hs_perm[1], 3: "colonial"}
                # Clue 5: The person in a ranch-style home is somewhere to the left of Peter.
                ranch_house = None
                for i in [1, 2, 3]:
                    if house_styles[i] == "ranch":
                        ranch_house = i
                if ranch_house is None:
                    continue
                # Determine Peter's house.
                peter_house = None
                for i in [1, 2, 3]:
                    if house_names[i] == "Peter":
                        peter_house = i
                        break
                if not (ranch_house < peter_house):
                    continue

                # Pet assignments: House 1 is fixed to "fish"
                for pet_perm in itertools.permutations(pet_options):
                    house_pets = {1: "fish", 2: pet_perm[0], 3: pet_perm[1]}
                    # Clue 7: Arnold has a cat.
                    valid = True
                    for i in [1, 2, 3]:
                        if house_names[i] == "Arnold" and house_pets[i] != "cat":
                            valid = False
                            break
                    if not valid:
                        continue

                    # Occupation assignments:
                    for occ_perm in itertools.permutations(occupations):
                        house_occ = {1: occ_perm[0], 2: occ_perm[1], 3: occ_perm[2]}
                        # Clue 9: The person who is an engineer is not in the third house.
                        if house_occ[3] == "engineer":
                            continue
                        # Clue 10: The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
                        tesla_house = None
                        teacher_house = None
                        for i in [1, 2, 3]:
                            if house_cars[i] == "tesla model 3":
                                tesla_house = i
                            if house_occ[i] == "teacher":
                                teacher_house = i
                        if tesla_house is None or teacher_house is None or not (tesla_house < teacher_house):
                            continue
                        # Clue 11: The person who owns a dog is the person who is an engineer.
                        # So in any house, if the occupation is engineer then pet must be dog,
                        # and if pet is dog then occupation must be engineer.
                        valid_pair = True
                        for i in [1, 2, 3]:
                            if house_occ[i] == "engineer" and house_pets[i] != "dog":
                                valid_pair = False
                            if house_pets[i] == "dog" and house_occ[i] != "engineer":
                                valid_pair = False
                        if not valid_pair:
                            continue

                        # Clue 8: Eric is somewhere to the left of the person who enjoys mountain retreats.
                        # Since house 3 vacation is mountain, Eric must be in house 1 or 2.
                        eric_house = None
                        for i in [1, 2, 3]:
                            if house_names[i] == "Eric":
                                eric_house = i
                        if eric_house is None or not (eric_house < 3):
                            continue

                        # All clues satisfied, compile solution for houses 1, 2, 3.
                        rows = []
                        for i in [1, 2, 3]:
                            row = [
                                str(i),
                                house_names[i],
                                house_cars[i],
                                house_styles[i],
                                house_pets[i],
                                house_occ[i],
                                vacations[i]
                            ]
                            rows.append(row)
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                                "rows": rows
                            }
                        }
                        solutions.append(solution)
    # Assuming a unique solution, output the first one found.
    if solutions:
        print(json.dumps(solutions[0]))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    solve()