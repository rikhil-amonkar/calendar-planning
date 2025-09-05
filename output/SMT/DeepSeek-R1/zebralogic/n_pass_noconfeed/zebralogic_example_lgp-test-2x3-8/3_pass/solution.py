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
        # Collect variables in lists for easier access
        names = [name1, name2]
        birthdays = [birthday1, birthday2]
        mothers = [mother1, mother2]
        
        rows = []
        for i in range(2):
            # Convert model evaluations to string and remove quotes
            name_val = str(m.eval(names[i])).replace('"', '')
            birthday_val = str(m.eval(birthdays[i])).replace('"', '')
            mother_val = str(m.eval(mothers[i])).replace('"', '')
            rows.append([str(i+1), name_val, birthday_val, mother_val])
        
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