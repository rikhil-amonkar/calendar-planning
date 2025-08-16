import json
from z3 import *

def solve_housing_puzzle():
    # Initialize the solver
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the attributes
    names = ["Alice", "Arnold", "Eric", "Peter", "Bob", "Carol"]
    occupations = ["engineer", "artist", "doctor", "teacher", "nurse", "lawyer"]
    car_models = ["chevrolet silverado", "ford f150", "honda civic", 
                  "toyota camry", "bmw 3 series", "tesla model 3"]

    # Create variables for each attribute in each house
    name_vars = {h: Int(f"name_{h}") for h in houses}
    occupation_vars = {h: Int(f"occupation_{h}") for h in houses}
    car_vars = {h: Int(f"car_{h}") for h in houses}

    # Add constraints that each attribute is one of the possible values
    for h in houses:
        s.add(And(name_vars[h] >= 0, name_vars[h] < len(names)))
        s.add(And(occupation_vars[h] >= 0, occupation_vars[h] < len(occupations)))
        s.add(And(car_vars[h] >= 0, car_vars[h] < len(car_models)))

    # Add uniqueness constraints for each attribute type
    s.add(Distinct([name_vars[h] for h in houses]))
    s.add(Distinct([occupation_vars[h] for h in houses]))
    s.add(Distinct([car_vars[h] for h in houses]))

    # Helper functions to get index of attributes
    def name_idx(name): return names.index(name)
    def occupation_idx(occ): return occupations.index(occ)
    def car_idx(car): return car_models.index(car)

    # Apply the clues one by one

    # Clue 1: The person who owns a Ford F-150 is in the fifth house.
    s.add(car_vars[5] == car_idx("ford f150"))

    # Clue 2: The person who owns a Chevrolet Silverado is not in the second house.
    s.add(car_vars[2] != car_idx("chevrolet silverado"))

    # Clue 3: The person who owns a Honda Civic and Peter are next to each other.
    for h in houses:
        if h > 1:
            s.add(Implies(car_vars[h] == car_idx("honda civic"), 
                         name_vars[h-1] == name_idx("Peter")))
            s.add(Implies(name_vars[h] == name_idx("Peter"), 
                         car_vars[h-1] == car_idx("honda civic")))
        if h < 6:
            s.add(Implies(car_vars[h] == car_idx("honda civic"), 
                         name_vars[h+1] == name_idx("Peter")))
            s.add(Implies(name_vars[h] == name_idx("Peter"), 
                         car_vars[h+1] == car_idx("honda civic")))

    # Clue 4: The person who is a lawyer is not in the fifth house.
    s.add(occupation_vars[5] != occupation_idx("lawyer"))

    # Clue 5: The person who is a nurse is directly left of the person who is an artist.
    for h in houses:
        if h < 6:
            s.add(Implies(occupation_vars[h] == occupation_idx("nurse"), 
                         occupation_vars[h+1] == occupation_idx("artist")))
        else:
            s.add(occupation_vars[h] != occupation_idx("nurse"))

    # Clue 6: Carol is somewhere to the right of Eric.
    # Find the house where Eric is and ensure Carol is in a higher-numbered house
    for h_eric in houses:
        for h_carol in houses:
            if h_carol <= h_eric:
                s.add(Not(And(name_vars[h_eric] == name_idx("Eric"), 
                          name_vars[h_carol] == name_idx("Carol"))))

    # Clue 7: The person who is a doctor is Eric.
    for h in houses:
        s.add(Implies(occupation_vars[h] == occupation_idx("doctor"), 
                     name_vars[h] == name_idx("Eric")))

    # Clue 8: The person who is a teacher is somewhere to the left of the person who is a nurse.
    # For each nurse, there must be a teacher in a lower-numbered house
    for h_nurse in houses:
        if h_nurse > 1:
            teacher_exists = Or([occupation_vars[h] == occupation_idx("teacher") 
                               for h in range(1, h_nurse)])
            s.add(Implies(occupation_vars[h_nurse] == occupation_idx("nurse"), 
                         teacher_exists))

    # Clue 9: Carol is not in the sixth house.
    s.add(name_vars[6] != name_idx("Carol"))

    # Clue 10: The person who is an engineer is Bob.
    for h in houses:
        s.add(Implies(occupation_vars[h] == occupation_idx("engineer"), 
                     name_vars[h] == name_idx("Bob")))

    # Clue 11: The person who owns a Toyota Camry is the person who is a nurse.
    for h in houses:
        s.add(Implies(car_vars[h] == car_idx("toyota camry"), 
                     occupation_vars[h] == occupation_idx("nurse")))
        s.add(Implies(occupation_vars[h] == occupation_idx("nurse"), 
                     car_vars[h] == car_idx("toyota camry")))

    # Clue 12: There is one house between Peter and the person who is a lawyer.
    for h_peter in houses:
        if h_peter + 2 <= 6:
            s.add(Implies(name_vars[h_peter] == name_idx("Peter"), 
                         occupation_vars[h_peter + 2] == occupation_idx("lawyer")))
        if h_peter - 2 >= 1:
            s.add(Implies(name_vars[h_peter] == name_idx("Peter"), 
                         occupation_vars[h_peter - 2] == occupation_idx("lawyer")))

    # Clue 13: There is one house between the person who owns a Tesla Model 3 and Bob.
    for h_tesla in houses:
        if h_tesla + 2 <= 6:
            s.add(Implies(car_vars[h_tesla] == car_idx("tesla model 3"), 
                         name_vars[h_tesla + 2] == name_idx("Bob")))
        if h_tesla - 2 >= 1:
            s.add(Implies(car_vars[h_tesla] == car_idx("tesla model 3"), 
                         name_vars[h_tesla - 2] == name_idx("Bob")))

    # Clue 14: Arnold is the person who is an artist.
    for h in houses:
        s.add(Implies(name_vars[h] == name_idx("Arnold"), 
                     occupation_vars[h] == occupation_idx("artist")))
        s.add(Implies(occupation_vars[h] == occupation_idx("artist"), 
                     name_vars[h] == name_idx("Arnold")))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "CarModel"],
                "rows": []
            }
        }
        
        # Extract the values for each house
        for h in sorted(houses):
            name = names[model[name_vars[h]].as_long()]
            occupation = occupations[model[occupation_vars[h]].as_long()]
            car = car_models[model[car_vars[h]].as_long()]
            solution["solution"]["rows"].append([str(h), name, occupation, car])
        
        return json.dumps(solution, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

# Print the solution
print(solve_housing_puzzle())