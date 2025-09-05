import json
from z3 import *

def main():
    solver = Solver()
    
    # House indices
    houses = [1, 2, 3, 4, 5, 6]
    
    # Attribute mappings
    names = {"Arnold": 0, "Eric": 1, "Bob": 2, "Alice": 3, "Carol": 4, "Peter": 5}
    mothers = {"Sarah": 0, "Holly": 1, "Janelle": 2, "Aniya": 3, "Penny": 4, "Kailyn": 5}
    pets = {"hamster": 0, "dog": 1, "bird": 2, "cat": 3, "fish": 4, "rabbit": 5}
    
    # Reverse mappings for output
    rev_names = {v: k for k, v in names.items()}
    rev_mothers = {v: k for k, v in mothers.items()}
    rev_pets = {v: k for k, v in pets.items()}
    
    # Variables for each house: name, mother, pet
    n = [Int(f"n_{i}") for i in houses]
    m = [Int(f"m_{i}") for i in houses]
    p = [Int(f"p_{i}") for i in houses]
    
    # All attributes must be in range [0,5]
    for i in houses:
        solver.add(And(n[i-1] >= 0, n[i-1] <= 5))
        solver.add(And(m[i-1] >= 0, m[i-1] <= 5))
        solver.add(And(p[i-1] >= 0, p[i-1] <= 5))
    
    # All attributes distinct per category
    solver.add(Distinct(n))
    solver.add(Distinct(m))
    solver.add(Distinct(p))
    
    # Helper variables for specific attribute houses
    cat_house = Int("cat_house")
    rabbit_house = Int("rabbit_house")
    dog_house = Int("dog_house")
    hamster_house = Int("hamster_house")
    fish_house = Int("fish_house")
    holly_mother_house = Int("holly_mother_house")
    janelle_mother_house = Int("janelle_mother_house")
    aniya_mother_house = Int("aniya_mother_house")
    kailyn_mother_house = Int("kailyn_mother_house")
    sarah_mother_house = Int("sarah_mother_house")
    bob_house = Int("bob_house")
    eric_house = Int("eric_house")
    alice_house = Int("alice_house")
    carol_house = Int("carol_house")
    arnold_house = Int("arnold_house")
    
    # Define house variables based on attributes
    for i in houses:
        solver.add(If(p[i-1] == pets["cat"], cat_house == i, True))
        solver.add(If(p[i-1] == pets["rabbit"], rabbit_house == i, True))
        solver.add(If(p[i-1] == pets["dog"], dog_house == i, True))
        solver.add(If(p[i-1] == pets["hamster"], hamster_house == i, True))
        solver.add(If(p[i-1] == pets["fish"], fish_house == i, True))
        solver.add(If(m[i-1] == mothers["Holly"], holly_mother_house == i, True))
        solver.add(If(m[i-1] == mothers["Janelle"], janelle_mother_house == i, True))
        solver.add(If(m[i-1] == mothers["Aniya"], aniya_mother_house == i, True))
        solver.add(If(m[i-1] == mothers["Kailyn"], kailyn_mother_house == i, True))
        solver.add(If(m[i-1] == mothers["Sarah"], sarah_mother_house == i, True))
        solver.add(If(n[i-1] == names["Bob"], bob_house == i, True))
        solver.add(If(n[i-1] == names["Eric"], eric_house == i, True))
        solver.add(If(n[i-1] == names["Alice"], alice_house == i, True))
        solver.add(If(n[i-1] == names["Carol"], carol_house == i, True))
        solver.add(If(n[i-1] == names["Arnold"], arnold_house == i, True))
    
    # Clue 1: Bob is not in the second house.
    solver.add(bob_house != 2)
    
    # Clue 2: Two houses between cat and rabbit.
    solver.add(Or(
        cat_house - rabbit_house == 3,
        rabbit_house - cat_house == 3
    ))
    
    # Clue 3: Cat directly left of Holly mother.
    solver.add(cat_house == holly_mother_house - 1)
    
    # Clue 4: Hamster directly left of rabbit.
    solver.add(hamster_house == rabbit_house - 1)
    
    # Clue 5: Rabbit owner is Eric.
    solver.add(n[rabbit_house-1] == names["Eric"])
    
    # Clue 6: One house between dog and cat.
    solver.add(Or(
        dog_house - cat_house == 2,
        cat_house - dog_house == 2
    ))
    
    # Clue 7: Cat owner has mother Janelle.
    solver.add(m[cat_house-1] == mothers["Janelle"])
    
    # Clue 8: Alice directly left of Carol.
    solver.add(alice_house == carol_house - 1)
    
    # Clue 9: Carol has mother Aniya.
    solver.add(m[carol_house-1] == mothers["Aniya"])
    
    # Clue 10: Arnold has cat.
    solver.add(arnold_house == cat_house)
    
    # Clue 11: Kailyn mother has rabbit.
    solver.add(m[rabbit_house-1] == mothers["Kailyn"])
    
    # Clue 12: Fish owner has mother Sarah.
    solver.add(m[fish_house-1] == mothers["Sarah"])
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare solution data
        rows = []
        for i in houses:
            idx = i-1
            name_val = model.evaluate(n[idx]).as_long()
            mother_val = model.evaluate(m[idx]).as_long()
            pet_val = model.evaluate(p[idx]).as_long()
            
            rows.append([
                str(i),
                rev_names[name_val],
                rev_mothers[mother_val],
                rev_pets[pet_val]
            ])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Mother", "Pet"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()