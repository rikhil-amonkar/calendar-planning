from z3 import *
import json

def main():
    # Define the enums for attributes
    Name, (Peter, Arnold, Eric) = EnumSort('Name', ['Peter', 'Arnold', 'Eric'])
    Occupation, (doctor, teacher, engineer) = EnumSort('Occupation', ['doctor', 'teacher', 'engineer'])
    Hobby, (cooking, photography, gardening) = EnumSort('Hobby', ['cooking', 'photography', 'gardening'])
    
    # Create variables for each house
    houses = [1, 2, 3]
    names = [Const(f'name_{i}', Name) for i in houses]
    occupations = [Const(f'occupation_{i}', Occupation) for i in houses]
    hobbies = [Const(f'hobby_{i}', Hobby) for i in houses]
    
    s = Solver()
    
    # All attributes are distinct
    s.add(Distinct(names))
    s.add(Distinct(occupations))
    s.add(Distinct(hobbies))
    
    # Clue 1: The doctor and Eric are next to each other
    s.add(Or(
        And(occupations[0] == doctor, names[1] == Eric),
        And(occupations[1] == doctor, Or(names[0] == Eric, names[2] == Eric)),
        And(occupations[2] == doctor, names[1] == Eric)
    ))
    
    # Clue 2: Cooking is directly left of teacher
    s.add(Or(
        And(hobbies[0] == cooking, occupations[1] == teacher),
        And(hobbies[1] == cooking, occupations[2] == teacher)
    ))
    
    # Clue 3: Doctor is right of gardening
    s.add(Or(
        And(hobbies[0] == gardening, Or(occupations[1] == doctor, occupations[2] == doctor)),
        And(hobbies[1] == gardening, occupations[2] == doctor)
    ))
    
    # Clue 4: Photography enthusiast is the teacher
    for i in range(3):
        s.add((occupations[i] == teacher) == (hobbies[i] == photography))
    
    # Clue 5: Engineer is Peter
    for i in range(3):
        s.add((occupations[i] == engineer) == (names[i] == Peter))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(3):
            # Get values from model
            n_val = m.evaluate(names[i])
            o_val = m.evaluate(occupations[i])
            h_val = m.evaluate(hobbies[i])
            
            # Convert to strings
            name_str = "Peter" if n_val == Peter else "Arnold" if n_val == Arnold else "Eric"
            occ_str = "doctor" if o_val == doctor else "teacher" if o_val == teacher else "engineer"
            hobby_str = "cooking" if h_val == cooking else "photography" if h_val == photography else "gardening"
            
            rows.append([str(i+1), name_str, occ_str, hobby_str])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()