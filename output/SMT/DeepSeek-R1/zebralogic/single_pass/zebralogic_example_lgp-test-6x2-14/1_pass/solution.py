from z3 import *
import json

def main():
    # Create the solver
    s = Solver()
    
    # Define variables for the unknown names: house2 and house4
    name1 = String('name1')  # for house2
    name3 = String('name3')  # for house4
    
    # Define variables for the unknown cigars: house1, house2, house4, house6
    cigar0 = String('cigar0')  # for house1
    cigar1 = String('cigar1')  # for house2
    cigar3 = String('cigar3')  # for house4
    cigar5 = String('cigar5')  # for house6
    
    # Constraints for names: must be "Arnold" or "Alice" and distinct
    s.add(Or(name1 == "Arnold", name1 == "Alice"))
    s.add(Or(name3 == "Arnold", name3 == "Alice"))
    s.add(name1 != name3)
    
    # Constraints for cigars: must be one of the remaining and distinct
    cigar_set = ["blends", "yellow monster", "dunhill", "prince"]
    s.add(Distinct(cigar0, cigar1, cigar3, cigar5))
    for c_var in [cigar0, cigar1, cigar3, cigar5]:
        s.add(Or([c_var == StringVal(val) for val in cigar_set]))
    
    # Clue 1: Arnold is left of blends smoker
    s.add(Or(
        And(name1 == "Arnold", Or(cigar3 == "blends", cigar5 == "blends")),
        And(name3 == "Arnold", cigar5 == "blends")
    ))
    
    # Clue 3: Arnold is left of prince smoker
    s.add(Or(
        And(name1 == "Arnold", Or(cigar3 == "prince", cigar5 == "prince")),
        And(name3 == "Arnold", cigar5 == "prince")
    ))
    
    # Clue 4: One house between Yellow Monster and blends
    s.add(Or(
        And(cigar1 == "yellow monster", cigar3 == "blends"),
        And(cigar1 == "blends", cigar3 == "yellow monster"),
        And(cigar3 == "yellow monster", cigar5 == "blends"),
        And(cigar3 == "blends", cigar5 == "yellow monster")
    ))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract values
        name1_val = m[name1].as_string()
        name3_val = m[name3].as_string()
        cigar0_val = m[cigar0].as_string()
        cigar1_val = m[cigar1].as_string()
        cigar3_val = m[cigar3].as_string()
        cigar5_val = m[cigar5].as_string()
        
        # Build the solution rows
        rows = [
            ["1", "Peter", cigar0_val],
            ["2", name1_val, cigar1_val],
            ["3", "Bob", "pall mall"],
            ["4", name3_val, cigar3_val],
            ["5", "Carol", "blue master"],
            ["6", "Eric", cigar5_val]
        ]
        
        # Create the result dictionary
        result = {
            "solution": {
                "header": ["House", "Name", "Cigar"],
                "rows": rows
            }
        }
        
        # Output the JSON
        print(json.dumps(result))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()