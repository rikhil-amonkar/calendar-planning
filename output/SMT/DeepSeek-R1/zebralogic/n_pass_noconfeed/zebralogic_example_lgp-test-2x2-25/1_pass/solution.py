from z3 import *
import json

def main():
    # Define the Enum sorts for Name and Vacation
    Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    Vacation, (beach, mountain) = EnumSort('Vacation', ['beach', 'mountain'])
    
    # Create variables for each house's attributes
    names = [Const(f'name_{i}', Name) for i in range(2)]
    vacations = [Const(f'vacation_{i}', Vacation) for i in range(2)]
    
    s = Solver()
    
    # Add constraint that all names are unique
    s.add(Distinct(names))
    # Add constraint that all vacations are unique
    s.add(Distinct(vacations))
    
    # Clue 1: Arnold is somewhere to the right of the person who loves beach vacations.
    # We'll determine the house numbers where Arnold and beach are located
    arnold_house_num = Int('arnold_house_num')
    beach_house_num = Int('beach_house_num')
    
    # Constraints to set the house numbers for Arnold and beach
    s.add(Or([And(names[i] == Arnold, arnold_house_num == i+1) for i in range(2)]))
    s.add(Or([And(vacations[i] == beach, beach_house_num == i+1) for i in range(2)]))
    s.add(arnold_house_num > beach_house_num)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        
        # Prepare the solution rows
        rows = []
        for i in range(2):
            house_num = str(i+1)
            name_val = m.eval(names[i])
            vac_val = m.eval(vacations[i])
            
            # Convert Z3 constants to strings
            if name_val == Arnold:
                name_str = "Arnold"
            else:
                name_str = "Eric"
                
            if vac_val == beach:
                vac_str = "beach"
            else:
                vac_str = "mountain"
                
            rows.append([house_num, name_str, vac_str])
        
        # Construct the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": rows
            }
        }
        
        # Output the JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()