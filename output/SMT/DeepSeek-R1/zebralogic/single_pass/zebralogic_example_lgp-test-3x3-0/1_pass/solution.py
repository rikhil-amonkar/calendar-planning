from z3 import *
import json

def main():
    # Define the enums for attributes
    Name = Datatype('Name')
    Name.declare('Peter')
    Name.declare('Eric')
    Name.declare('Arnold')
    Name = Name.create()
    
    Education = Datatype('Education')
    Education.declare('bachelor')
    Education.declare('associate')
    Education.declare('high_school')
    Education = Education.create()
    
    Occupation = Datatype('Occupation')
    Occupation.declare('teacher')
    Occupation.declare('doctor')
    Occupation.declare('engineer')
    Occupation = Occupation.create()
    
    # Create variables for each house
    n1, n2, n3 = Consts('n1 n2 n3', Name)
    e1, e2, e3 = Consts('e1 e2 e3', Education)
    o1, o2, o3 = Consts('o1 o2 o3', Occupation)
    
    s = Solver()
    
    # All names are distinct
    s.add(Distinct(n1, n2, n3))
    # All educations are distinct
    s.add(Distinct(e1, e2, e3))
    # All occupations are distinct
    s.add(Distinct(o1, o2, o3))
    
    # Clue 1: The teacher is directly left of the associate's degree
    s.add(Or(
        And(o1 == Occupation.teacher, e2 == Education.associate),
        And(o2 == Occupation.teacher, e3 == Education.associate)
    ))
    
    # Clue 2: The associate's degree and Eric are adjacent
    s.add(Or(
        And(e1 == Education.associate, n2 == Name.Eric),
        And(e2 == Education.associate, Or(n1 == Name.Eric, n3 == Name.Eric)),
        And(e3 == Education.associate, n2 == Name.Eric)
    ))
    
    # Clue 3: Peter has the high school diploma
    s.add(Or(
        And(n1 == Name.Peter, e1 == Education.high_school),
        And(n2 == Name.Peter, e2 == Education.high_school),
        And(n3 == Name.Peter, e3 == Education.high_school)
    ))
    
    # Clue 4: The doctor has the bachelor's degree
    s.add(Or(
        And(o1 == Occupation.doctor, e1 == Education.bachelor),
        And(o2 == Occupation.doctor, e2 == Education.bachelor),
        And(o3 == Occupation.doctor, e3 == Education.bachelor)
    ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        
        # Helper functions to convert Z3 values to strings
        def name_to_str(val):
            if eq(val, Name.Peter):
                return "Peter"
            elif eq(val, Name.Eric):
                return "Eric"
            elif eq(val, Name.Arnold):
                return "Arnold"
            else:
                return "Unknown"
        
        def edu_to_str(val):
            if eq(val, Education.bachelor):
                return "bachelor"
            elif eq(val, Education.associate):
                return "associate"
            elif eq(val, Education.high_school):
                return "high school"
            else:
                return "Unknown"
        
        def occ_to_str(val):
            if eq(val, Occupation.teacher):
                return "teacher"
            elif eq(val, Occupation.doctor):
                return "doctor"
            elif eq(val, Occupation.engineer):
                return "engineer"
            else:
                return "Unknown"
        
        # Extract values for each house
        house1 = ["1", name_to_str(m[n1]), edu_to_str(m[e1]), occ_to_str(m[o1])]
        house2 = ["2", name_to_str(m[n2]), edu_to_str(m[e2]), occ_to_str(m[o2])]
        house3 = ["3", name_to_str(m[n3]), edu_to_str(m[e3]), occ_to_str(m[o3])]
        
        # Construct the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Education", "Occupation"],
                "rows": [house1, house2, house3]
            }
        }
        
        # Output as JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()