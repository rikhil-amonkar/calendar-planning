from z3 import *
import json

def main():
    # Define the attributes using EnumSort
    Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    Birthday, (april, sept) = EnumSort('Birthday', ['april', 'sept'])
    Mother, (Aniya, Holly) = EnumSort('Mother', ['Aniya', 'Holly'])
    
    # Create variables for each house
    name1, name2 = Consts('name1 name2', Name)
    birthday1, birthday2 = Consts('birthday1 birthday2', Birthday)
    mother1, mother2 = Consts('mother1 mother2', Mother)
    
    s = Solver()
    
    # Each attribute has unique values across houses
    s.add(Distinct([name1, name2]))
    s.add(Distinct([birthday1, birthday2]))
    s.add(Distinct([mother1, mother2]))
    
    # Clue 1: Eric is left of person with mother Holly
    s.add(name1 == Eric)
    s.add(mother2 == Holly)
    
    # Clue 2: April birthday in first house
    s.add(birthday1 == april)
    
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(1, 3):
            name_val = m.eval(globals()[f'name{i}']).name()
            birthday_val = m.eval(globals()[f'birthday{i}']).name()
            mother_val = m.eval(globals()[f'mother{i}']).name()
            rows.append([str(i), name_val, birthday_val, mother_val])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Birthday", "Mother"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()