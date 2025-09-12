from z3 import *
import json

def main():
    s = Solver()

    # Define the lists for mapping
    names_list = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occupations_list = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    cars_list = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    # Create variables for each house (1-6, indexes 0-5)
    name = [Int(f'name_h{i+1}') for i in range(6)]
    occupation = [Int(f'occupation_h{i+1}') for i in range(6)]
    car = [Int(f'car_h{i+1}') for i in range(6)]

    # Add constraints that each category is a permutation (distinct and 0-5)
    for var_list in [name, occupation, car]:
        s.add(Distinct(var_list))
        for v in var_list:
            s.add(And(0 <= v, v <= 5))

    # Now add the puzzle constraints

    # Clue 1: Ford F-150 is in fifth house (index 4)
    s.add(car[4] == 1)  # ford f150 is index 1

    # Clue 2: Chevrolet Silverado not in second house (index 1)
    s.add(car[1] != 0)  # chevrolet is index 0

    # Clue 3: Honda Civic (2) and Peter (3) are next to each other
    for i in range(6):
        for j in range(6):
            s.add(Implies(And(car[i] == 2, name[j] == 3), Abs(i - j) == 1))

    # Clue 4: Lawyer (5) not in fifth house (index 4)
    s.add(occupation[4] != 5)

    # Clue 5: Nurse (4) directly left of artist (1)
    clue5 = Or([And(occupation[i] == 4, occupation[i+1] == 1) for i in range(5)])
    s.add(clue5)

    # Clue 6: Carol (5) is to the right of Eric (2)
    for i in range(6):
        for j in range(6):
            s.add(Implies(And(name[i] == 5, name[j] == 2), i > j))

    # Clue 7: Doctor (2) is Eric (2)
    for i in range(6):
        s.add(Implies(name[i] == 2, occupation[i] == 2))

    # Clue 8: Teacher (3) is to the left of nurse (4)
    clue8 = Or([And(occupation[i] == 3, occupation[j] == 4, i < j) for i in range(6) for j in range(i+1, 6)])
    s.add(clue8)

    # Clue 9: Carol (5) not in sixth house (index 5)
    s.add(name[5] != 5)

    # Clue 10: Engineer (0) is Bob (4)
    for i in range(6):
        s.add(Implies(name[i] == 4, occupation[i] == 0))

    # Clue 11: Toyota Camry (3) is nurse (4)
    for i in range(6):
        s.add(Implies(car[i] == 3, occupation[i] == 4))

    # Clue 12: One house between Peter (3) and lawyer (5)
    for i in range(6):
        for j in range(6):
            s.add(Implies(And(name[i] == 3, occupation[j] == 5), Abs(i - j) == 2))

    # Clue 13: One house between Tesla (5) and Bob (4)
    for i in range(6):
        for j in range(6):
            s.add(Implies(And(car[i] == 5, name[j] == 4), Abs(i - j) == 2))

    # Clue 14: Arnold (1) is artist (1)
    for i in range(6):
        s.add(Implies(name[i] == 1, occupation[i] == 1))

    # Now check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        # Now extract the solution
        solution = []
        for i in range(6):  # for each house (0-5, which is 1-6)
            house_num = i + 1
            name_idx = model[name[i]].as_long()
            occ_idx = model[occupation[i]].as_long()
            car_idx = model[car[i]].as_long()
            solution.append([
                str(house_num),
                names_list[name_idx],
                occupations_list[occ_idx],
                cars_list[car_idx]
            ])
        # Now format as JSON
        result = {
            "solution": {
                "header": ["House", "Name", "Occupation", "CarModel"],
                "rows": solution
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()