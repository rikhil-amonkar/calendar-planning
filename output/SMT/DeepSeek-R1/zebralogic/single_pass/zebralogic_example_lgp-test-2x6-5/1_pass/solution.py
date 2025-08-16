from z3 import Solver, StringVal, Const, StringSort, Or, And, Implies, Not, sat

def main():
    s = Solver()
    
    # Define variables for house 1 (index0) and house 2 (index1)
    names = [Const(f'name{i}', StringSort()) for i in range(2)]
    occupations = [Const(f'occupation{i}', StringSort()) for i in range(2)]
    birthdays = [Const(f'birthday{i}', StringSort()) for i in range(2)]
    houseStyles = [Const(f'houseStyle{i}', StringSort()) for i in range(2)]
    heights = [Const(f'height{i}', StringSort()) for i in range(2)]
    cigars = [Const(f'cigar{i}', StringSort()) for i in range(2)]
    
    # Define the domains for each attribute
    name_domain = ["Arnold", "Eric"]
    occupation_domain = ["engineer", "doctor"]
    birthday_domain = ["april", "sept"]
    houseStyle_domain = ["victorian", "colonial"]
    height_domain = ["very short", "short"]
    cigar_domain = ["pall mall", "prince"]
    
    # Each attribute must be one of the domain values and distinct between houses
    for i in range(2):
        s.add(Or([names[i] == StringVal(n) for n in name_domain]))
        s.add(Or([occupations[i] == StringVal(o) for o in occupation_domain]))
        s.add(Or([birthdays[i] == StringVal(b) for b in birthday_domain]))
        s.add(Or([houseStyles[i] == StringVal(h) for h in houseStyle_domain]))
        s.add(Or([heights[i] == StringVal(h) for h in height_domain]))
        s.add(Or([cigars[i] == StringVal(c) for c in cigar_domain]))
    
    s.add(names[0] != names[1])
    s.add(occupations[0] != occupations[1])
    s.add(birthdays[0] != birthdays[1])
    s.add(houseStyles[0] != houseStyles[1])
    s.add(heights[0] != heights[1])
    s.add(cigars[0] != cigars[1])
    
    # Clue 1: The engineer is in the first house.
    s.add(occupations[0] == StringVal("engineer"))
    
    # Clue 2: The person with April birthday and the doctor are next to each other (adjacent houses).
    s.add(Or(
        And(birthdays[0] == StringVal("april"), occupations[1] == StringVal("doctor")),
        And(birthdays[1] == StringVal("april"), occupations[0] == StringVal("doctor"))
    ))
    
    # Clue 3: The colonial-style house is the engineer's house.
    s.add(Or(
        And(houseStyles[0] == StringVal("colonial"), occupations[0] == StringVal("engineer")),
        And(houseStyles[1] == StringVal("colonial"), occupations[1] == StringVal("engineer"))
    ))
    
    # Clue 4: The very short person is the engineer.
    s.add(Or(
        And(heights[0] == StringVal("very short"), occupations[0] == StringVal("engineer")),
        And(heights[1] == StringVal("very short"), occupations[1] == StringVal("engineer"))
    ))
    
    # Clue 5: The short person prefers Pall Mall cigars.
    for i in range(2):
        s.add(Implies(heights[i] == StringVal("short"), cigars[i] == StringVal("pall mall")))
    
    # Clue 6: The engineer is Eric.
    s.add(Or(
        And(occupations[0] == StringVal("engineer"), names[0] == StringVal("Eric")),
        And(occupations[1] == StringVal("engineer"), names[1] == StringVal("Eric"))
    ))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                "rows": []
            }
        }
        for i in range(2):
            house_num = str(i+1)
            name_val = m[names[i]].as_string()
            occupation_val = m[occupations[i]].as_string()
            birthday_val = m[birthdays[i]].as_string()
            houseStyle_val = m[houseStyles[i]].as_string()
            height_val = m[heights[i]].as_string()
            cigar_val = m[cigars[i]].as_string()
            row = [house_num, name_val, occupation_val, birthday_val, houseStyle_val, height_val, cigar_val]
            solution["solution"]["rows"].append(row)
        
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()