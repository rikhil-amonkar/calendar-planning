import json
from z3 import *

def main():
    # Define variables for each house
    name1 = String('name1')
    name2 = String('name2')
    birthday1 = String('birthday1')
    birthday2 = String('birthday2')
    mother1 = String('mother1')
    mother2 = String('mother2')
    
    s = Solver()
    
    # Possible values for names, birthdays, and mothers
    s.add(Or(name1 == 'Arnold', name1 == 'Eric'))
    s.add(Or(name2 == 'Arnold', name2 == 'Eric'))
    s.add(name1 != name2)
    
    s.add(Or(birthday1 == 'april', birthday1 == 'sept'))
    s.add(Or(birthday2 == 'april', birthday2 == 'sept'))
    s.add(birthday1 != birthday2)
    
    s.add(Or(mother1 == 'Aniya', mother1 == 'Holly'))
    s.add(Or(mother2 == 'Aniya', mother2 == 'Holly'))
    s.add(mother1 != mother2)
    
    # Clue 1: Eric is to the left of the person with mother Holly
    s.add(name1 == 'Eric')
    s.add(mother2 == 'Holly')
    
    # Clue 2: Birthday in April is in house 1
    s.add(birthday1 == 'april')
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Extract values
        house1_row = [
            "1",
            str(m[name1]),
            str(m[birthday1]),
            str(m[mother1])
        ]
        house2_row = [
            "2",
            str(m[name2]),
            str(m[birthday2]),
            str(m[mother2])
        ]
        
        # Construct the result dictionary
        result = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother"],
                "rows": [house1_row, house2_row]
            }
        }
        print(json.dumps(result))
    else:
        # In case no solution is found
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()