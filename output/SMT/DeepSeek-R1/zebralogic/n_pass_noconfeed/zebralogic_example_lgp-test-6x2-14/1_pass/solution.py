import json
from z3 import *

def main():
    # Define the attributes
    name_list = ['Carol', 'Peter', 'Eric', 'Arnold', 'Alice', 'Bob']
    cigar_identifiers = ['blends', 'yellow_monster', 'pall_mall', 'blue_master', 'dunhill', 'prince']
    cigar_output = ['blends', 'yellow monster', 'pall mall', 'blue master', 'dunhill', 'prince']
    
    # Create enum sorts
    NameSort, name_consts = EnumSort('Name', name_list)
    CigarSort, cigar_consts = EnumSort('Cigar', cigar_identifiers)
    
    # Create variables for each house
    names = [Const(f'name_{i}', NameSort) for i in range(6)]
    cigars = [Const(f'cigar_{i}', CigarSort) for i in range(6)]
    
    solver = Solver()
    
    # All names and cigars are distinct
    solver.add(Distinct(names))
    solver.add(Distinct(cigars))
    
    # Fixed assignments from clues
    solver.add(names[0] == name_consts[1])  # House 1: Peter
    solver.add(names[2] == name_consts[5])  # House 3: Bob
    solver.add(names[4] == name_consts[0])  # House 5: Carol
    solver.add(names[5] == name_consts[2])  # House 6: Eric
    solver.add(cigars[2] == cigar_consts[2])  # House 3: pall mall
    solver.add(cigars[4] == cigar_consts[3])  # House 5: blue master
    
    # Clue 1: Arnold left of blends smoker
    arnold_house = Int('arnold_house')
    blends_house = Int('blends_house')
    solver.add(arnold_house >= 0, arnold_house < 6)
    solver.add(blends_house >= 0, blends_house < 6)
    for i in range(6):
        solver.add(If(names[i] == name_consts[3], arnold_house == i, True))
        solver.add(If(cigars[i] == cigar_consts[0], blends_house == i, True))
    solver.add(arnold_house < blends_house)
    
    # Clue 3: Arnold left of prince smoker
    prince_house = Int('prince_house')
    solver.add(prince_house >= 0, prince_house < 6)
    for i in range(6):
        solver.add(If(cigars[i] == cigar_consts[5], prince_house == i, True))
    solver.add(arnold_house < prince_house)
    
    # Clue 4: One house between Yellow Monster and blends
    yellow_house = Int('yellow_house')
    solver.add(yellow_house >= 0, yellow_house < 6)
    for i in range(6):
        solver.add(If(cigars[i] == cigar_consts[1], yellow_house == i, True))
    solver.add(Or(yellow_house == blends_house + 2, yellow_house == blends_house - 2))
    
    # Check and get the solution
    if solver.check() == sat:
        model = solver.model()
        result = {
            "solution": {
                "header": ["House", "Name", "Cigar"],
                "rows": []
            }
        }
        for i in range(6):
            n_val = model[names[i]]
            c_val = model[cigars[i]]
            n_str = None
            for j in range(len(name_consts)):
                if n_val == name_consts[j]:
                    n_str = name_list[j]
                    break
            c_str = None
            for j in range(len(cigar_consts)):
                if c_val == cigar_consts[j]:
                    c_str = cigar_output[j]
                    break
            result["solution"]["rows"].append([str(i+1), n_str, c_str])
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()