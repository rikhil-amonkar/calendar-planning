import json
from z3 import *

def solve_scheduling_problem():
    # Create the solver
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4, 5, 6]

    # Define the names and phone models
    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = ["huawei p50", "iphone 13", "xiaomi mi 11", "oneplus 9", "samsung galaxy s21", "google pixel 6"]

    # Create variables for each house's name and phone
    name_vars = [Int(f"name_{h}") for h in houses]
    phone_vars = [Int(f"phone_{h}") for h in houses]

    # Add constraints that names and phones are within their valid indices
    for h in houses:
        s.add(And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        s.add(And(phone_vars[h-1] >= 0, phone_vars[h-1] < len(phones)))

    # All names and phones must be distinct
    s.add(Distinct(name_vars))
    s.add(Distinct(phone_vars))

    # Create name and phone mappings for easier constraint writing
    name_map = {names[i]: i for i in range(len(names))}
    phone_map = {phones[i]: i for i in range(len(phones))}

    # Apply the clues
    # Clue 2: The person who uses a Huawei P50 is in the first house.
    s.add(phone_vars[0] == phone_map["huawei p50"])
    
    # Clue 7: The person who uses a Huawei P50 is Eric.
    s.add(name_vars[0] == name_map["Eric"])
    
    # Clue 3: The person who uses a OnePlus 9 is in the sixth house.
    s.add(phone_vars[5] == phone_map["oneplus 9"])
    
    # Clue 10: Arnold is the person who uses a OnePlus 9.
    s.add(name_vars[5] == name_map["Arnold"])
    
    # Clue 8: The person who uses a Xiaomi Mi 11 is in the third house.
    s.add(phone_vars[2] == phone_map["xiaomi mi 11"])
    
    # Clue 1: The person who uses an iPhone 13 is Alice.
    for h in houses:
        s.add(Implies(phone_vars[h-1] == phone_map["iphone 13"], name_vars[h-1] == name_map["Alice"]))
    
    # Clue 5: The person who uses an iPhone 13 is not in the second house.
    s.add(phone_vars[1] != phone_map["iphone 13"])
    
    # Clue 4: The person who uses a Google Pixel 6 is not in the second house.
    s.add(phone_vars[1] != phone_map["google pixel 6"])
    
    # Clue 6: There is one house between Bob and Carol.
    bob_pos = Int("bob_pos")
    carol_pos = Int("carol_pos")
    s.add(Or(
        And(bob_pos + 2 == carol_pos),
        And(carol_pos + 2 == bob_pos)
    ))
    # Connect positions to actual houses
    for h in houses:
        s.add(Implies(name_vars[h-1] == name_map["Bob"], bob_pos == h))
        s.add(Implies(name_vars[h-1] == name_map["Carol"], carol_pos == h))
    
    # Clue 9: Alice is somewhere to the left of Carol.
    alice_pos = Int("alice_pos")
    for h in houses:
        s.add(Implies(name_vars[h-1] == name_map["Alice"], alice_pos == h))
    s.add(alice_pos < carol_pos)

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "PhoneModel"],
                "rows": []
            }
        }
        
        # Collect the results
        for h in houses:
            name_idx = model.evaluate(name_vars[h-1]).as_long()
            phone_idx = model.evaluate(phone_vars[h-1]).as_long()
            solution["solution"]["rows"].append([
                str(h),
                names[name_idx],
                phones[phone_idx]
            ])
        
        return solution
    else:
        return {"error": "No solution found"}

# Solve the problem and print the JSON result
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))