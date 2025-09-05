from z3 import *
import json

def main():
    solver = Solver()
    numHouses = 6  # Houses 1..6, indices 0..5

    # Define mappings for attributes
    names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    car_models = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

    # Create variables for each house: each house gets a name, an occupation, and a car model.
    name_vars = [Int(f"name_{i}") for i in range(numHouses)]
    occ_vars = [Int(f"occ_{i}") for i in range(numHouses)]
    car_vars = [Int(f"car_{i}") for i in range(numHouses)]
    
    # Domain constraints: each attribute variable is between 0 and 5.
    for i in range(numHouses):
        solver.add(name_vars[i] >= 0, name_vars[i] < 6)
        solver.add(occ_vars[i] >= 0, occ_vars[i] < 6)
        solver.add(car_vars[i] >= 0, car_vars[i] < 6)
        
    # All attributes must be unique across houses.
    solver.add(Distinct(name_vars))
    solver.add(Distinct(occ_vars))
    solver.add(Distinct(car_vars))
    
    # Clue 1: The person who owns a Ford F-150 is in the fifth house.
    # "ford f150" is index 1, and house 5 is index 4.
    solver.add(car_vars[4] == 1)
    
    # Clue 2: The person who owns a Chevrolet Silverado is not in the second house.
    # "chevrolet silverado" is index 0; house 2 is index 1.
    solver.add(car_vars[1] != 0)
    
    # Clue 3: The person who owns a Honda Civic and Peter are next to each other.
    # "honda civic" is index 2 and "Peter" is index 3.
    for i in range(numHouses):
        for j in range(numHouses):
            solver.add(Implies(And(name_vars[i] == 3, car_vars[j] == 2), Or(j == i + 1, j == i - 1)))
    
    # Clue 4: The person who is a lawyer is not in the fifth house.
    # "lawyer" is index 5 and house 5 is index 4.
    solver.add(occ_vars[4] != 5)
    
    # Clue 5: The person who is a nurse is directly left of the person who is an artist.
    # "nurse" is index 4 and "artist" is index 1.
    for i in range(numHouses):
        solver.add(Implies(occ_vars[i] == 4, And(i < numHouses - 1, occ_vars[i+1] == 1)))
    
    # Clue 6: Carol is somewhere to the right of Eric.
    # "Carol" is index 5, "Eric" is index 2.
    for i in range(numHouses):
        for j in range(numHouses):
            solver.add(Implies(And(name_vars[i] == 5, name_vars[j] == 2), i > j))
    
    # Clue 7: The person who is a doctor is Eric.
    # "doctor" is index 2 and "Eric" is index 2.
    for i in range(numHouses):
        solver.add(Implies(occ_vars[i] == 2, name_vars[i] == 2))
        solver.add(Implies(name_vars[i] == 2, occ_vars[i] == 2))
    
    # Clue 8: The person who is a teacher is somewhere to the left of the person who is a nurse.
    # "teacher" is index 3 and "nurse" is index 4.
    for i in range(numHouses):
        for j in range(numHouses):
            solver.add(Implies(And(occ_vars[i] == 3, occ_vars[j] == 4), i < j))
    
    # Clue 9: Carol is not in the sixth house.
    # "Carol" is index 5 and house 6 is index 5.
    solver.add(name_vars[5] != 5)
    
    # Clue 10: The person who is an engineer is Bob.
    # "engineer" is index 0 and "Bob" is index 4.
    for i in range(numHouses):
        solver.add(Implies(occ_vars[i] == 0, name_vars[i] == 4))
        solver.add(Implies(name_vars[i] == 4, occ_vars[i] == 0))
    
    # Clue 11: The person who owns a Toyota Camry is the person who is a nurse.
    # "toyota camry" is index 3 and "nurse" is index 4.
    for i in range(numHouses):
        solver.add(Implies(car_vars[i] == 3, occ_vars[i] == 4))
        solver.add(Implies(occ_vars[i] == 4, car_vars[i] == 3))
    
    # Clue 12: There is one house between Peter and the person who is a lawyer.
    # "Peter" is index 3 and "lawyer" is index 5.
    for i in range(numHouses):
        for j in range(numHouses):
            solver.add(Implies(And(name_vars[i] == 3, occ_vars[j] == 5), Or(j == i + 2, j == i - 2)))
    
    # Clue 13: There is one house between the person who owns a Tesla Model 3 and Bob.
    # "tesla model 3" is index 5 and "Bob" is index 4.
    for i in range(numHouses):
        for j in range(numHouses):
            solver.add(Implies(And(car_vars[i] == 5, name_vars[j] == 4), Or(j == i + 2, j == i - 2)))
    
    # Clue 14: Arnold is the person who is an artist.
    # "Arnold" is index 1 and "artist" is index 1.
    for i in range(numHouses):
        solver.add(Implies(name_vars[i] == 1, occ_vars[i] == 1))
        solver.add(Implies(occ_vars[i] == 1, name_vars[i] == 1))
    
    # Solve and output the solution as JSON
    if solver.check() == sat:
        model = solver.model()
        solution_rows = []
        for i in range(numHouses):
            house_num = str(i + 1)
            name_val = model.evaluate(name_vars[i]).as_long()
            occ_val = model.evaluate(occ_vars[i]).as_long()
            car_val = model.evaluate(car_vars[i]).as_long()
            solution_rows.append([house_num, names[name_val], occupations[occ_val], car_models[car_val]])
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "CarModel"],
                "rows": solution_rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": {"header": ["House", "Name", "Occupation", "CarModel"], "rows": []}}))

if __name__ == "__main__":
    main()