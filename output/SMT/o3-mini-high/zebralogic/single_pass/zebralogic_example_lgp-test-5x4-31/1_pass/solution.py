from z3 import *
import json

def main():
    # There are 5 houses indexed 0..4 (corresponding to houses 1..5)
    houses = range(5)
    
    # For each house we have four attributes: Name, Vacation, Child, Nationality.
    # We'll use integers to denote the values as follows:
    # Names:   0:"Alice", 1:"Bob", 2:"Arnold", 3:"Eric", 4:"Peter"
    # Vacations: 0:"cruise", 1:"city", 2:"camping", 3:"beach", 4:"mountain"
    # Children: 0:"Bella", 1:"Samantha", 2:"Fred", 3:"Meredith", 4:"Timothy"
    # Nationalities: 0:"dane", 1:"norwegian", 2:"brit", 3:"german", 4:"swede"
    
    names      = [Int(f"name_{i}")      for i in houses]
    vacations  = [Int(f"vacation_{i}")  for i in houses]
    children   = [Int(f"child_{i}")     for i in houses]
    nationalities = [Int(f"nat_{i}")     for i in houses]
    
    s = Solver()
    
    # Each attribute value is in 0..4 for every house.
    for i in houses:
        s.add(And(names[i]  >= 0, names[i]  < 5))
        s.add(And(vacations[i] >= 0, vacations[i] < 5))
        s.add(And(children[i]  >= 0, children[i]  < 5))
        s.add(And(nationalities[i] >= 0, nationalities[i] < 5))
    
    # All attributes are unique across houses.
    s.add(Distinct(names))
    s.add(Distinct(vacations))
    s.add(Distinct(children))
    s.add(Distinct(nationalities))
    
    # Clue 1: "The Norwegian is Peter."
    # For every house, if the nationality is norwegian (1) then the name must be Peter (4), and vice‐versa.
    for i in houses:
        s.add(Or(nationalities[i] != 1, names[i] == 4))
        s.add(Or(names[i] != 4, nationalities[i] == 1))
    
    # Clue 2: "The Swedish person’s child is named Bella."
    # If a house’s nationality is swede (4) then its child must be Bella (0).
    for i in houses:
        s.add(Or(nationalities[i] != 4, children[i] == 0))
    
    # Clue 3: "The person who loves beach vacations is directly left of the person whose child is named Samantha."
    # If a house (except the last) has vacation beach (3), then the house immediately to its right must have child Samantha (1).
    # Also, the last house cannot have vacation beach.
    s.add(vacations[4] != 3)
    for i in range(4):
        s.add(Or(vacations[i] != 3, children[i+1] == 1))
    
    # Clue 4: "The person whose child is named Bella is not in the second house."
    # House 2 means index 1.
    s.add(children[1] != 0)
    
    # Clue 5: "Alice is the British person."
    # If a house has Alice (0) then its nationality must be brit (2).
    for i in houses:
        s.add(Or(names[i] != 0, nationalities[i] == 2))
    
    # Clue 6: "The person who likes going on cruises is in the first house."
    # House 1 means index 0; cruise is 0.
    s.add(vacations[0] == 0)
    
    # Clue 7: "The person whose child is named Meredith is in the fourth house."
    # House 4 means index 3; Meredith is 3.
    s.add(children[3] == 3)
    
    # Clue 8: "Eric is not in the fifth house."
    # Eric is 3; House 5 is index 4.
    s.add(names[4] != 3)
    
    # Clue 9: "The Swedish person is somewhere to the right of the Norwegian."
    # Since there is exactly one norwegian and one swede, the index of the house with norwegian (1) must be less than that of swede (4).
    s.add(Sum([If(nationalities[i] == 1, i, 0) for i in houses]) < 
          Sum([If(nationalities[i] == 4, i, 0) for i in houses]))
    
    # Clue 10: "There is one house between the person whose child is named Fred and the person who prefers city breaks."
    # Fred is 2; city is 1.
    for i in houses:
        # If house i has child Fred, then either the house two to the left or two to the right must have vacation city.
        conds = []
        if i - 2 >= 0:
            conds.append(vacations[i-2] == 1)
        if i + 2 < 5:
            conds.append(vacations[i+2] == 1)
        s.add(Or(children[i] != 2, Or(conds)))
    
    # Clue 11: "Bob is the person who enjoys camping trips."
    # Bob is 1; camping is 2.
    for i in houses:
        s.add(Or(names[i] != 1, vacations[i] == 2))
    
    # Clue 12: "The Dane is in the fifth house."
    # Dane is 0; House 5 is index 4.
    s.add(nationalities[4] == 0)
    
    # Clue 13: "The person who enjoys camping trips is not in the fifth house."
    s.add(vacations[4] != 2)
    
    # Solve the puzzle.
    if s.check() == sat:
        m = s.model()
        # Define the mapping dictionaries (as defined above).
        names_map = {0:"Alice", 1:"Bob", 2:"Arnold", 3:"Eric", 4:"Peter"}
        vacation_map = {0:"cruise", 1:"city", 2:"camping", 3:"beach", 4:"mountain"}
        child_map = {0:"Bella", 1:"Samantha", 2:"Fred", 3:"Meredith", 4:"Timothy"}
        nat_map = {0:"dane", 1:"norwegian", 2:"brit", 3:"german", 4:"swede"}
        
        # Build the solution rows for houses 1 to 5 (house number as string).
        rows = []
        for i in houses:
            row = [
                str(i+1),
                names_map[m[names[i]].as_long()],
                vacation_map[m[vacations[i]].as_long()],
                child_map[m[children[i]].as_long()],
                nat_map[m[nationalities[i]].as_long()]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Children", "Nationality"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()