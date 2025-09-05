from z3 import *
import json

def main():
    # Define the enums for each attribute using EnumSort
    Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    Occupation, (engineer, doctor) = EnumSort('Occupation', ['engineer', 'doctor'])
    Birthday, (april, sept) = EnumSort('Birthday', ['april', 'sept'])
    HouseStyle, (victorian, colonial) = EnumSort('HouseStyle', ['victorian', 'colonial'])
    Height, (very_short, short) = EnumSort('Height', ['very_short', 'short'])
    Cigar, (pall_mall, prince) = EnumSort('Cigar', ['pall_mall', 'prince'])
    
    # Create variables for each house attribute
    houses = [1, 2]
    name_vars = [Const(f'name_{i}', Name) for i in houses]
    occupation_vars = [Const(f'occupation_{i}', Occupation) for i in houses]
    birthday_vars = [Const(f'birthday_{i}', Birthday) for i in houses]
    housestyle_vars = [Const(f'housestyle_{i}', HouseStyle) for i in houses]
    height_vars = [Const(f'height_{i}', Height) for i in houses]
    cigar_vars = [Const(f'cigar_{i}', Cigar) for i in houses]
    
    s = Solver()
    
    # Add uniqueness constraints for each attribute
    s.add(Distinct(name_vars))
    s.add(Distinct(occupation_vars))
    s.add(Distinct(birthday_vars))
    s.add(Distinct(housestyle_vars))
    s.add(Distinct(height_vars))
    s.add(Distinct(cigar_vars))
    
    # Clue 1: The person who is an engineer is in the first house.
    s.add(occupation_vars[0] == engineer)
    
    # Clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
    s.add(Or(
        And(birthday_vars[0] == april, occupation_vars[1] == doctor),
        And(birthday_vars[1] == april, occupation_vars[0] == doctor)
    ))
    
    # Clue 3: The person living in a colonial-style house is the person who is an engineer.
    for i in range(2):
        s.add(Implies(housestyle_vars[i] == colonial, occupation_vars[i] == engineer))
        s.add(Implies(occupation_vars[i] == engineer, housestyle_vars[i] == colonial))
    
    # Clue 4: The person who is very short is the person who is an engineer.
    for i in range(2):
        s.add(Implies(height_vars[i] == very_short, occupation_vars[i] == engineer))
        s.add(Implies(occupation_vars[i] == engineer, height_vars[i] == very_short))
    
    # Clue 5: The person who is short is the person partial to Pall Mall.
    for i in range(2):
        s.add(Implies(height_vars[i] == short, cigar_vars[i] == pall_mall))
        s.add(Implies(cigar_vars[i] == pall_mall, height_vars[i] == short))
    
    # Clue 6: The person who is an engineer is Eric.
    s.add(name_vars[0] == Eric)
    
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(2):
            n_val = m.eval(name_vars[i])
            o_val = m.eval(occupation_vars[i])
            b_val = m.eval(birthday_vars[i])
            hs_val = m.eval(housestyle_vars[i])
            h_val = m.eval(height_vars[i])
            c_val = m.eval(cigar_vars[i])
            
            # Convert enum values to strings and replace underscores
            n_str = str(n_val)
            o_str = str(o_val)
            b_str = str(b_val)
            hs_str = str(hs_val)
            h_str = str(h_val).replace('_', ' ')
            c_str = str(c_val).replace('_', ' ')
            
            rows.append([str(i+1), n_str, o_str, b_str, hs_str, h_str, c_str])
        
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                "rows": rows
            }
        }
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()