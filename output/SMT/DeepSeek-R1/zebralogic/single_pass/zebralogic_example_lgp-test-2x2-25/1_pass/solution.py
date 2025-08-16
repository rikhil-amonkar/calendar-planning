from z3 import *
import json

def main():
    # Define enums for names and vacations
    Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    Vacation, (beach, mountain) = EnumSort('Vacation', ['beach', 'mountain'])
    
    # Create variables for each house
    n1 = Const('n1', Name)
    n2 = Const('n2', Name)
    v1 = Const('v1', Vacation)
    v2 = Const('v2', Vacation)
    
    s = Solver()
    
    # Add distinct constraints for names and vacations
    s.add(Distinct(n1, n2))
    s.add(Distinct(v1, v2))
    
    # Apply the clue: Arnold is to the right of the beach lover
    s.add(v1 == beach)
    s.add(n2 == Arnold)
    
    if s.check() == sat:
        m = s.model()
        
        # Helper function to convert Z3 enum to string
        def enum_to_string(val):
            return val.decl().name()
        
        # Create rows for each house
        row1 = ["1", enum_to_string(m[n1]), enum_to_string(m[v1])]
        row2 = ["2", enum_to_string(m[n2]), enum_to_string(m[v2])]
        
        # Construct the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Vacation"],
                "rows": [row1, row2]
            }
        }
        print(json.dumps(solution_dict))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()