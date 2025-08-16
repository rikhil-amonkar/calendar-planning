from z3 import *
import json

def solve():
    # People and occupations
    persons = ["Arnold", "Eric", "Peter", "Alice"]
    # Create integer variables for house numbers
    house = {p: Int("house_" + p) for p in persons}
    # Create integer variables for occupations.
    # Let's use: 1 = doctor, 2 = engineer, 3 = artist, 4 = teacher.
    occ = {p: Int("occ_" + p) for p in persons}
    
    DOCTOR, ENGINEER, ARTIST, TEACHER = 1, 2, 3, 4

    # Initialize solver
    s = Solver()
    
    # Each house is numbered 1 to 4 and each person has a house.
    for p in persons:
        s.add(house[p] >= 1, house[p] <= 4)
        s.add(Or(occ[p] == DOCTOR, occ[p] == ENGINEER, occ[p] == ARTIST, occ[p] == TEACHER))
    
    # All houses and occupations must be distinct.
    s.add(Distinct([house[p] for p in persons]))
    s.add(Distinct([occ[p] for p in persons]))
    
    # Clue 1: There are two houses between Eric and Peter.
    s.add(Abs(house["Eric"] - house["Peter"]) == 3)
    
    # Clue 2: The person who is a teacher is Peter.
    s.add(occ["Peter"] == TEACHER)
    
    # Clue 3: Peter is not in the first house.
    s.add(house["Peter"] != 1)
    
    # Clue 5: The person who is an artist is Alice.
    s.add(occ["Alice"] == ARTIST)
    
    # Clue 4: There is one house between the person who is a doctor and Alice.
    # For the unique person who is a doctor (occ == DOCTOR), the absolute difference between
    # their house and Alice's house must be 2.
    for p in persons:
        s.add(Implies(occ[p] == DOCTOR, Abs(house[p] - house["Alice"]) == 2))
    
    # Check for a solution.
    if s.check() == sat:
        m = s.model()
        # Build a mapping from house number to (Name, Occupation)
        occupation_name = {DOCTOR: "doctor", ENGINEER: "engineer", ARTIST: "artist", TEACHER: "teacher"}
        houses_solution = {}
        for p in persons:
            h = m[house[p]].as_long()
            occ_val = m[occ[p]].as_long()
            houses_solution[h] = [p, occupation_name[occ_val]]
        
        # Build the rows sorted by house number (from 1 to 4)
        rows = []
        for h in range(1, 5):
            person_name, occ_str = houses_solution[h]
            rows.append([str(h), person_name, occ_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Occupation"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print("No solution found.")

if __name__ == "__main__":
    solve()