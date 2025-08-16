from z3 import *
import json

def main():
    # Define the Name datatype
    Name = Datatype('Name')
    Name.declare('Arnold')
    Name.declare('Eric')
    Name.declare('Peter')
    Name.declare('Alice')
    Name = Name.create()
    
    # Define the Occupation datatype
    Occupation = Datatype('Occupation')
    Occupation.declare('doctor')
    Occupation.declare('engineer')
    Occupation.declare('artist')
    Occupation.declare('teacher')
    Occupation = Occupation.create()
    
    # Create arrays for names and occupations for 4 houses
    n = [Const('n0', Name), Const('n1', Name), Const('n2', Name), Const('n3', Name)]
    o = [Const('o0', Occupation), Const('o1', Occupation), Const('o2', Occupation), Const('o3', Occupation)]
    
    s = Solver()
    
    # Clue 1 and 3: Eric and Peter have two houses between them, and Peter is not in the first house.
    # Therefore, Eric must be in house1 (index0) and Peter in house4 (index3).
    s.add(n[0] == Name.Eric)
    s.add(n[3] == Name.Peter)
    
    # Clue 2: Peter is the teacher -> house4 (index3) occupation is teacher.
    s.add(o[3] == Occupation.teacher)
    
    # All names and occupations are distinct
    s.add(Distinct(n[0], n[1], n[2], n[3])
    s.add(Distinct(o[0], o[1], o[2], o[3]))
    
    # Clue 5: The artist is Alice -> for the house where name is Alice, occupation is artist.
    for i in range(4):
        s.add(Implies(n[i] == Name.Alice, o[i] == Occupation.artist))
    
    # Clue 4: One house between the doctor and Alice -> |index(doctor) - index(Alice)| = 2.
    for i in range(4):
        conditions = []
        if i-2 >= 0:
            conditions.append(o[i-2] == Occupation.doctor)
        if i+2 < 4:
            conditions.append(o[i+2] == Occupation.doctor)
        if conditions:
            s.add(Implies(n[i] == Name.Alice, Or(conditions)))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(4):
            house_num = str(i+1)
            name_val = m.evaluate(n[i])
            occ_val = m.evaluate(o[i])
            name_str = name_val.decl().name()
            occ_str = occ_val.decl().name()
            rows.append([house_num, name_str, occ_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Occupation"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()