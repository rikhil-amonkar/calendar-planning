from z3 import *
import json

def main():
    solver = Solver()
    
    n_houses = 6
    houses = list(range(1, n_houses+1))
    
    # Define attributes
    names = ['Carol', 'Peter', 'Eric', 'Arnold', 'Alice', 'Bob']
    cigars = ['blends', 'yellow monster', 'pall mall', 'blue master', 'dunhill', 'prince']
    
    # Create variables for each attribute
    name_vars = [Int(f"name_{i}") for i in houses]
    cigar_vars = [Int(f"cigar_{i}") for i in houses]
    
    # Constraint: all name variables have values between 0 and 5
    for var in name_vars:
        solver.add(var >= 0, var < len(names))
    
    # Constraint: all cigar variables have values between 0 and 5
    for var in cigar_vars:
        solver.add(var >= 0, var < len(cigars))
    
    # Constraint: all names are distinct
    solver.add(Distinct(name_vars))
    
    # Constraint: all cigars are distinct
    solver.add(Distinct(cigar_vars))
    
    # Clue 2: The person who smokes Blue Master is in the fifth house.
    blue_master_index = cigars.index('blue master')
    solver.add(cigar_vars[4] == blue_master_index)
    
    # Clue 5: The person partial to Pall Mall is in the third house.
    pall_mall_index = cigars.index('pall mall')
    solver.add(cigar_vars[2] == pall_mall_index)
    
    # Clue 6: Eric is in the sixth house.
    eric_index = names.index('Eric')
    solver.add(name_vars[5] == eric_index)
    
    # Clue 8: Peter is in the first house.
    peter_index = names.index('Peter')
    solver.add(name_vars[0] == peter_index)
    
    # Clue 9: Bob is in the third house.
    bob_index = names.index('Bob')
    solver.add(name_vars[2] == bob_index)
    
    # Clue 7: Carol and Eric are next to each other.
    carol_index = names.index('Carol')
    eric_house = name_vars[5]  # Eric is in house 6
    # Carol must be in house 5 (since Eric is in 6)
    solver.add(name_vars[4] == carol_index)
    
    # Clue 1: Arnold is somewhere to the left of the person who smokes many unique blends.
    arnold_index = names.index('Arnold')
    blends_index = cigars.index('blends')
    # Find the house where Arnold is
    arnold_house = Int("arnold_house")
    blends_house = Int("blends_house")
    solver.add(arnold_house >= 1, arnold_house <= 6)
    solver.add(blends_house >= 1, blends_house <= 6)
    
    # Connect Arnold's house to the name variable
    for i in range(n_houses):
        solver.add(Implies(name_vars[i] == arnold_index, arnold_house == i+1))
    
    # Connect blends cigar to the cigar variable
    for i in range(n_houses):
        solver.add(Implies(cigar_vars[i] == blends_index, blends_house == i+1))
    
    solver.add(arnold_house < blends_house)
    
    # Clue 3: Arnold is somewhere to the left of the Prince smoker.
    prince_index = cigars.index('prince')
    prince_house = Int("prince_house")
    solver.add(prince_house >= 1, prince_house <= 6)
    
    for i in range(n_houses):
        solver.add(Implies(cigar_vars[i] == prince_index, prince_house == i+1))
    
    solver.add(arnold_house < prince_house)
    
    # Clue 4: There is one house between the person who smokes Yellow Monster and the person who smokes many unique blends.
    yellow_monster_index = cigars.index('yellow monster')
    yellow_monster_house = Int("yellow_monster_house")
    solver.add(yellow_monster_house >= 1, yellow_monster_house <= 6)
    
    for i in range(n_houses):
        solver.add(Implies(cigar_vars[i] == yellow_monster_index, yellow_monster_house == i+1))
    
    solver.add(Or(
        yellow_monster_house == blends_house - 2,
        yellow_monster_house == blends_house + 2
    ))
    
    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Extract the solution
        solution = []
        for i in range(n_houses):
            name_val = model.eval(name_vars[i]).as_long()
            cigar_val = model.eval(cigar_vars[i]).as_long()
            
            house_num = str(i + 1)
            name = names[name_val]
            cigar = cigars[cigar_val]
            
            solution.append([house_num, name, cigar])
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Cigar"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()