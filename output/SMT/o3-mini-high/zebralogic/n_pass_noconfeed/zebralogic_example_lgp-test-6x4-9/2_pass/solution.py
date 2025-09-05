from z3 import *
import json

def main():
    solver = Solver()
    num_houses = 6

    # Create Z3 integer arrays for each attribute.
    names   = [Int(f"name_{i}") for i in range(num_houses)]
    phones  = [Int(f"phone_{i}") for i in range(num_houses)]
    nats    = [Int(f"nat_{i}") for i in range(num_houses)]
    colors  = [Int(f"color_{i}") for i in range(num_houses)]
    
    # Domain constraints for each attribute (each value in 0..5).
    for i in range(num_houses):
        solver.add(And(names[i]  >= 0, names[i]  < 6))
        solver.add(And(phones[i] >= 0, phones[i] < 6))
        solver.add(And(nats[i]   >= 0, nats[i]   < 6))
        solver.add(And(colors[i] >= 0, colors[i] < 6))
    
    # All attributes must be all different (each is a permutation).
    solver.add(Distinct(names))
    solver.add(Distinct(phones))
    solver.add(Distinct(nats))
    solver.add(Distinct(colors))
    
    # Clue 1: Carol is not in the third house (index 2).
    solver.add(names[2] != 0)
    
    # Clue 2: There is one house between the Dane (nat == 3) and the British person (nat == 5).
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(nats[i] == 3, nats[j] == 5), Abs(i - j) == 2))
    
    # Clue 3: Carol is the person whose favorite color is green (green == 3).
    for i in range(num_houses):
        solver.add(Implies(names[i] == 0, colors[i] == 3))
    
    # Clue 4: Arnold is directly left of Alice. (Arnold == 3, Alice == 2)
    for i in range(num_houses - 1):
        solver.add(Implies(names[i] == 3, names[i+1] == 2))
    
    # Clue 5: Alice is the German. (Alice == 2, German nat == 4)
    for i in range(num_houses):
        solver.add(Implies(names[i] == 2, nats[i] == 4))
    
    # Clue 6: The person who uses a OnePlus 9 (phone == 4) is the person who loves purple (color == 5).
    # Replace Iff with an equivalent expression.
    for i in range(num_houses):
        solver.add((phones[i] == 4) == (colors[i] == 5))
    
    # Clue 7: The person who uses a Huawei P50 (phone == 3) is not in the third house.
    solver.add(phones[2] != 3)
    
    # Clue 8: The person who uses a Samsung Galaxy S21 (phone == 0) is in the fifth house (index 4).
    solver.add(phones[4] == 0)
    
    # Clue 9: The person who loves white (color == 4) is somewhere to the right of the person whose favorite color is red (color == 1).
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(colors[i] == 1, colors[j] == 4), i < j))
    
    # Clue 10: The person who uses a Samsung Galaxy S21 (phone == 0) is Bob (Bob == 1).
    for i in range(num_houses):
        solver.add(Implies(phones[i] == 0, names[i] == 1))
    
    # Clue 11: The Dane (nat == 3) is the person who loves yellow (color == 2).
    for i in range(num_houses):
        solver.add(Implies(nats[i] == 3, colors[i] == 2))
    
    # Clue 12: The person who uses a Samsung Galaxy S21 (phone == 0) is somewhere to the left of Peter (name == 5).
    for i in range(num_houses):
        for j in range(num_houses):
            solver.add(Implies(And(phones[i] == 0, names[j] == 5), i < j))
    
    # Clue 13: The person who loves blue (color == 0) is Peter (name == 5).
    for i in range(num_houses):
        solver.add(Implies(names[i] == 5, colors[i] == 0))
    
    # Clue 14: Peter (name == 5) is the British person (nat == 5).
    for i in range(num_houses):
        solver.add(Implies(names[i] == 5, nats[i] == 5))
    
    # Clue 15: The person who uses a Samsung Galaxy S21 (phone == 0) is directly left of the person who uses an iPhone 13 (phone == 2).
    for i in range(num_houses - 1):
        solver.add(Implies(phones[i] == 0, phones[i+1] == 2))
    
    # Clue 16: The Norwegian (nat == 2) is the person who loves purple (color == 5).
    for i in range(num_houses):
        solver.add(Implies(nats[i] == 2, colors[i] == 5))
    
    # Clue 17: The person who uses a Xiaomi Mi 11 (phone == 5) is the Chinese (nat == 1).
    for i in range(num_houses):
        solver.add(Implies(phones[i] == 5, nats[i] == 1))
    
    # Solve the puzzle.
    if solver.check() == sat:
        model = solver.model()
        # Reverse mapping dictionaries.
        name_map = {0: "Carol", 1: "Bob", 2: "Alice", 3: "Arnold", 4: "Eric", 5: "Peter"}
        phone_map = {
            0: "samsung galaxy s21",
            1: "google pixel 6",
            2: "iphone 13",
            3: "huawei p50",
            4: "oneplus 9",
            5: "xiaomi mi 11"
        }
        nat_map = {0: "swede", 1: "chinese", 2: "norwegian", 3: "dane", 4: "german", 5: "brit"}
        color_map = {0: "blue", 1: "red", 2: "yellow", 3: "green", 4: "white", 5: "purple"}
        
        # Build the solution dictionary.
        solution = {
            "solution": {
                "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                "rows": []
            }
        }
        
        for i in range(num_houses):
            house_number = str(i + 1)
            sol_row = [
                house_number,
                name_map[model[names[i]].as_long()],
                phone_map[model[phones[i]].as_long()],
                nat_map[model[nats[i]].as_long()],
                color_map[model[colors[i]].as_long()]
            ]
            solution["solution"]["rows"].append(sol_row)
        
        # Output the solution as a JSON formatted dictionary.
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()