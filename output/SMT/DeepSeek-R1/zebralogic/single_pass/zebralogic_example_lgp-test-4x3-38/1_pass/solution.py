from z3 import *
import json

def main():
    # Define the attribute mappings to integers
    names = {"Alice": 0, "Peter": 1, "Arnold": 2, "Eric": 3}
    mothers = {"Holly": 0, "Kailyn": 1, "Janelle": 2, "Aniya": 3}
    flowers = {"carnations": 0, "roses": 1, "lilies": 2, "daffodils": 3}
    
    # Reverse mappings for output
    rev_names = {v: k for k, v in names.items()}
    rev_mothers = {v: k for k, v in mothers.items()}
    rev_flowers = {v: k for k, v in flowers.items()}
    
    # Create Z3 variables for each house
    n = [Int('n0'), Int('n1'), Int('n2'), Int('n3')]
    m = [Int('m0'), Int('m1'), Int('m2'), Int('m3')]
    f = [Int('f0'), Int('f1'), Int('f2'), Int('f3')]
    
    s = Solver()
    
    # Each attribute per house is in [0,3]
    for i in range(4):
        s.add(n[i] >= 0, n[i] <= 3)
        s.add(m[i] >= 0, m[i] <= 3)
        s.add(f[i] >= 0, f[i] <= 3)
    
    # All attributes are distinct
    s.add(Distinct(n))
    s.add(Distinct(m))
    s.add(Distinct(f))
    
    # Fixed clues
    s.add(n[2] == names["Alice"])   # House 3: Alice
    s.add(m[2] == mothers["Kailyn"]) # House 3: Kailyn (Alice's mother)
    s.add(f[1] == flowers["lilies"]) # House 2: Lilies
    
    # Conditional constraints
    for i in range(4):
        s.add(Implies(n[i] == names["Arnold"], m[i] == mothers["Holly"]))  # Arnold's mother is Holly
        s.add(Implies(n[i] == names["Eric"], f[i] == flowers["daffodils"])) # Eric loves daffodils
    
    # Positional constraints
    # Arnold's house
    arnold_house = Int('arnold_house')
    s.add(arnold_house >= 0, arnold_house < 4)
    s.add(Or([And(n[i] == names["Arnold"], arnold_house == i) for i in range(4)]))
    
    # Janelle's mother house
    janelle_mother_house = Int('janelle_mother_house')
    s.add(janelle_mother_house >= 0, janelle_mother_house < 4)
    s.add(Or([And(m[i] == mothers["Janelle"], janelle_mother_house == i) for i in range(4)]))
    s.add(janelle_mother_house > arnold_house)  # Janelle's mother right of Arnold
    
    # Carnations house
    carnations_house = Int('carnations_house')
    s.add(carnations_house >= 0, carnations_house < 4)
    s.add(Or([And(f[i] == flowers["carnations"], carnations_house == i) for i in range(4)]))
    
    # Peter's house
    peter_house = Int('peter_house')
    s.add(peter_house >= 0, peter_house < 4)
    s.add(Or([And(n[i] == names["Peter"], peter_house == i) for i in range(4)]))
    s.add(peter_house > carnations_house)  # Peter right of carnations lover
    
    # Carnations right of Holly (Arnold's house)
    s.add(carnations_house > arnold_house)
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        solution_rows = []
        for i in range(4):
            house_num = str(i + 1)
            name_val = rev_names[model.evaluate(n[i]).as_long()]
            mother_val = rev_mothers[model.evaluate(m[i]).as_long()]
            flower_val = rev_flowers[model.evaluate(f[i]).as_long()]
            solution_rows.append([house_num, name_val, mother_val, flower_val])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Mother", "Flower"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()