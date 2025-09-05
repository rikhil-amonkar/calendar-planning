import json
from z3 import *

def main():
    solver = Solver()
    houses = [0, 1, 2]  # Using indices 0,1,2 for houses 1,2,3 respectively

    # Define variables for each house: name, occupation, hobby
    name_vars = [Int(f"name_{i}") for i in houses]
    occ_vars = [Int(f"occ_{i}") for i in houses]
    hobby_vars = [Int(f"hobby_{i}") for i in houses]

    # Domain constraints: each variable takes a value in {0, 1, 2}
    for var in name_vars + occ_vars + hobby_vars:
        solver.add(Or(var == 0, var == 1, var == 2))
    
    # Each attribute category must be unique among houses
    solver.add(Distinct(name_vars))
    solver.add(Distinct(occ_vars))
    solver.add(Distinct(hobby_vars))

    # Mappings (using integer constants):
    # Names: Peter = 0, Arnold = 1, Eric = 2
    # Occupations: doctor = 0, teacher = 1, engineer = 2
    # Hobbies: cooking = 0, photography = 1, gardening = 2

    # Clue 1: The person who is a doctor and Eric are next to each other.
    # For house 0: if doctor then neighbor (house 1) must be Eric.
    solver.add(Implies(occ_vars[0] == 0, name_vars[1] == 2))
    # For house 1: doctor must have Eric as either left or right neighbor.
    solver.add(Implies(occ_vars[1] == 0, Or(name_vars[0] == 2, name_vars[2] == 2)))
    # For house 2: if doctor then neighbor (house 1) must be Eric.
    solver.add(Implies(occ_vars[2] == 0, name_vars[1] == 2))
    
    # Clue 2: The person who loves cooking is directly left of the person who is a teacher.
    # Teacher cannot be in the leftmost house.
    solver.add(occ_vars[0] != 1)
    # If cooking is in house 0, then teacher must be in house 1.
    solver.add(Implies(hobby_vars[0] == 0, occ_vars[1] == 1))
    # If cooking is in house 1, then teacher must be in house 2.
    solver.add(Implies(hobby_vars[1] == 0, occ_vars[2] == 1))
    # Conversely, if teacher is in house 1, cooking must be in house 0.
    solver.add(Implies(occ_vars[1] == 1, hobby_vars[0] == 0))
    # If teacher is in house 2, cooking must be in house 1.
    solver.add(Implies(occ_vars[2] == 1, hobby_vars[1] == 0))
    
    # Clue 3: The person who is a doctor is somewhere to the right of the person who enjoys gardening.
    # For any house i (doctor) and house j (gardening), it must be that i > j.
    for i in houses:
        for j in houses:
            solver.add(Implies(And(occ_vars[i] == 0, hobby_vars[j] == 2), i > j))
    
    # Clue 4: The photography enthusiast is the person who is a teacher.
    # This creates a one-to-one relation between photography (1) and teacher (1).
    for i in houses:
        solver.add((hobby_vars[i] == 1) == (occ_vars[i] == 1))
    
    # Clue 5: The person who is an engineer is Peter.
    # This means that if a house is occupied by an engineer (2), then the name must be Peter (0)
    for i in houses:
        solver.add((occ_vars[i] == 2) == (name_vars[i] == 0))
    
    if solver.check() == sat:
        model = solver.model()
        # Mapping dictionaries for output
        name_map = {0: "Peter", 1: "Arnold", 2: "Eric"}
        occ_map = {0: "doctor", 1: "teacher", 2: "engineer"}
        hobby_map = {0: "cooking", 1: "photography", 2: "gardening"}
        
        rows = []
        for i in houses:
            house_num = str(i + 1)
            name_str = name_map[model[name_vars[i]].as_long()]
            occ_str = occ_map[model[occ_vars[i]].as_long()]
            hobby_str = hobby_map[model[hobby_vars[i]].as_long()]
            rows.append([house_num, name_str, occ_str, hobby_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()