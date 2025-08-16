from z3 import *

def main():
    # Define the enums for Name, Occupation, Hobby
    NameSort, (Peter_c, Arnold_c, Eric_c) = EnumSort('Name', ('Peter', 'Arnold', 'Eric'))
    OccupationSort, (doctor_c, teacher_c, engineer_c) = EnumSort('Occupation', ('doctor', 'teacher', 'engineer'))
    HobbySort, (cooking_c, photography_c, gardening_c) = EnumSort('Hobby', ('cooking', 'photography', 'gardening'))
    
    # Create variables for each house: names, occupations, hobbies
    n = [Const(f'n{i}', NameSort) for i in range(1,4)]
    o = [Const(f'o{i}', OccupationSort) for i in range(1,4)]
    h = [Const(f'h{i}', HobbySort) for i in range(1,4)]
    
    s = Solver()
    
    # All names, occupations, hobbies are distinct
    s.add(Distinct(n[0], n[1], n[2]))
    s.add(Distinct(o[0], o[1], o[2]))
    s.add(Distinct(h[0], h[1], h[2]))
    
    # Clue 1: The doctor and Eric are next to each other.
    s.add(Or(
        And(o[0] == doctor_c, n[1] == Eric_c),   # doctor in house1, Eric in house2
        And(o[1] == doctor_c, Or(n[0] == Eric_c, n[2] == Eric_c)), # doctor in house2, Eric in house1 or house3
        And(o[2] == doctor_c, n[1] == Eric_c)    # doctor in house3, Eric in house2
    ))
    
    # Clue 2: cooking is directly left of teacher.
    s.add(Or(
        And(h[0] == cooking_c, o[1] == teacher_c),  # cooking in house1, teacher in house2
        And(h[1] == cooking_c, o[2] == teacher_c)   # cooking in house2, teacher in house3
    ))
    
    # Clue 3: doctor is right of gardening.
    s.add(Or(
        And(h[0] == gardening_c, Or(o[1] == doctor_c, o[2] == doctor_c)), # gardening in house1, doctor in house2 or 3
        And(h[1] == gardening_c, o[2] == doctor_c)  # gardening in house2, doctor in house3
    ))
    
    # Clue 4: photography enthusiast is the teacher.
    for i in range(3):
        s.add( (h[i] == photography_c) == (o[i] == teacher_c) )
    
    # Clue 5: engineer is Peter.
    for i in range(3):
        s.add( (o[i] == engineer_c) == (n[i] == Peter_c) )
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Mapping from constants to strings
        const_to_name = {Peter_c: "Peter", Arnold_c: "Arnold", Eric_c: "Eric"}
        const_to_occ = {doctor_c: "doctor", teacher_c: "teacher", engineer_c: "engineer"}
        const_to_hobby = {cooking_c: "cooking", photography_c: "photography", gardening_c: "gardening"}
        
        # Prepare the rows
        rows = []
        for i in range(3):
            name_val = model.eval(n[i])
            occ_val = model.eval(o[i])
            hobby_val = model.eval(h[i])
            name_str = const_to_name[name_val]
            occ_str = const_to_occ[occ_val]
            hobby_str = const_to_hobby[hobby_val]
            rows.append([str(i+1), name_str, occ_str, hobby_str])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Hobby"],
                "rows": rows
            }
        }
        
        # Print as JSON string
        import json
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()