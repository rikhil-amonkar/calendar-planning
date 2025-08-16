from z3 import Solver, Int, Distinct, Or, And, sat
import json

def main():
    # Define the lists for names and vacations
    names_list = ['Alice', 'Bob', 'Carol', 'Eric', 'Peter', 'Arnold']
    vac_list = ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach']
    
    # Create Z3 variables for names and vacations for 6 houses
    n = [Int(f'n{i}') for i in range(6)]
    v = [Int(f'v{i}') for i in range(6)]
    
    s = Solver()
    
    # Each variable must be in [0,5]
    for i in range(6):
        s.add(n[i] >= 0, n[i] < 6)
        s.add(v[i] >= 0, v[i] < 6)
    
    # All names and vacations are distinct
    s.add(Distinct(n))
    s.add(Distinct(v))
    
    # Clue 2: Eric is right of Alice -> Alice in house1 (index0), Eric in house2 (index1)
    s.add(n[0] == names_list.index('Alice'))
    s.add(n[1] == names_list.index('Eric'))
    
    # Clue 4: Cultural tours in house3 (index2)
    s.add(v[2] == vac_list.index('cultural'))
    
    # Clue 7: Cultural tours is Peter -> house3 name is Peter
    s.add(n[2] == names_list.index('Peter'))
    
    # Clue 9: City break in house4 (index3)
    s.add(v[3] == vac_list.index('city'))
    
    # Clue 8: Cruise is Bob -> for the house where name is Bob, vacation is cruise
    bob_index = names_list.index('Bob')
    cruise_index = vac_list.index('cruise')
    s.add(Or([And(n[i] == bob_index, v[i] == cruise_index) for i in range(6)]))
    
    # Clue 5: Bob directly left of Arnold
    arnold_index = names_list.index('Arnold')
    s.add(Or([And(n[i] == bob_index, n[i+1] == arnold_index) for i in range(5)]))
    
    # Clue 6: Camping not in house1 (index0)
    camping_index = vac_list.index('camping')
    s.add(v[0] != camping_index)
    
    # Clue 1: Cultural tours (house3, index2) left of beach
    beach_index = vac_list.index('beach')
    s.add(Or(v[3] == beach_index, v[4] == beach_index, v[5] == beach_index))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Build the solution rows
        rows = []
        for i in range(6):
            house_num = str(i+1)
            name_val = model[n[i]].as_long()
            vac_val = model[v[i]].as_long()
            name_str = names_list[name_val]
            vac_str = vac_list[vac_val]
            rows.append([house_num, name_str, vac_str])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
        # Output as JSON
        print(json.dumps(solution_dict))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()