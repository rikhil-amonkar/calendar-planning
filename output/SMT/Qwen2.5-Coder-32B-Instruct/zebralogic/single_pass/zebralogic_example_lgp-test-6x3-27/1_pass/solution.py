from z3 import *

# Define variables
houses = range(1, 7)
names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
car_models = ["chevrolet silverado", "ford f150", "honda civic", "toyota camry", "bmw 3 series", "tesla model 3"]

# Create dictionaries to map each entity to a variable
name_vars = {name: Int(f"name_{name}") for name in names}
occupation_vars = {occupation: Int(f"occupation_{occupation}") for occupation in occupations}
car_model_vars = {car_model: Int(f"car_model_{car_model}") for car_model in car_models}

# Create a solver instance
solver = Solver()

# Add constraints for unique placement
for entity_vars in [name_vars, occupation_vars, car_model_vars]:
    solver.add(Distinct([entity_vars[entity] for entity in entity_vars]))

# Add constraints for house numbers
for entity_vars in [name_vars, occupation_vars, car_model_vars]:
    for entity in entity_vars:
        solver.add(entity_vars[entity] >= 1)
        solver.add(entity_vars[entity] <= 6)

# Clue 1: The person who owns a Ford F-150 is in the fifth house.
solver.add(car_model_vars["ford f150"] == 5)

# Clue 2: The person who owns a Chevrolet Silverado is not in the second house.
solver.add(car_model_vars["chevrolet silverado"] != 2)

# Clue 3: The person who owns a Honda Civic and Peter are next to each other.
solver.add(Abs(car_model_vars["honda civic"] - name_vars["Peter"]) == 1)

# Clue 4: The person who is a lawyer is not in the fifth house.
solver.add(occupation_vars["lawyer"] != 5)

# Clue 5: The person who is a nurse is directly left of the person who is an artist.
solver.add(occupation_vars["nurse"] + 1 == occupation_vars["artist"])

# Clue 6: Carol is somewhere to the right of Eric.
solver.add(name_vars["Carol"] > name_vars["Eric"])

# Clue 7: The person who is a doctor is Eric.
solver.add(occupation_vars["doctor"] == name_vars["Eric"])

# Clue 8: The person who is a teacher is somewhere to the left of the person who is a nurse.
solver.add(occupation_vars["teacher"] < occupation_vars["nurse"])

# Clue 9: Carol is not in the sixth house.
solver.add(name_vars["Carol"] != 6)

# Clue 10: The person who is an engineer is Bob.
solver.add(occupation_vars["engineer"] == name_vars["Bob"])

# Clue 11: The person who owns a Toyota Camry is the person who is a nurse.
solver.add(car_model_vars["toyota camry"] == occupation_vars["nurse"])

# Clue 12: There is one house between Peter and the person who is a lawyer.
solver.add(Abs(name_vars["Peter"] - occupation_vars["lawyer"]) == 2)

# Clue 13: There is one house between the person who owns a Tesla Model 3 and Bob.
solver.add(Abs(car_model_vars["tesla model 3"] - name_vars["Bob"]) == 2)

# Clue 14: Arnold is the person who is an artist.
solver.add(name_vars["Arnold"] == occupation_vars["artist"])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the solution in the required format
    solution = {"solution": {"header": ["House", "Name", "Occupation", "CarModel"], "rows": []}}
    for house in houses:
        name = next(name for name, var in name_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        occupation = next(occupation for occupation, var in occupation_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        car_model = next(car_model for car_model, var in car_model_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        solution["solution"]["rows"].append([str(house), name, occupation, car_model])
    
    print(solution)
else:
    print("No solution found")