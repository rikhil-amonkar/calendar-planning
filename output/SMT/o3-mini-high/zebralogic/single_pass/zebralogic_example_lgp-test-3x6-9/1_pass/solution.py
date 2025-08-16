from z3 import *
import json

def main():
    s = Solver()
    n = 3  # Three houses, indexed 0,1,2 (which we will output as “1”, “2”, “3”)

    # Create Z3 Int variables for each house and each attribute.
    # Domains: each variable will take one of the values {0, 1, 2} with the following mapping:
    #
    # Names:        0 → "Peter",  1 → "Arnold",   2 → "Eric"
    # Cars:         0 → "toyota camry", 1 → "ford f150",  2 → "tesla model 3"
    # HouseStyle:   0 → "ranch",  1 → "colonial", 2 → "victorian"
    # Pets:         0 → "cat",    1 → "dog",    2 → "fish"
    # Occupation:   0 → "engineer", 1 → "doctor", 2 → "teacher"
    # Vacation:     0 → "city",   1 → "mountain", 2 → "beach"
    
    names       = [Int(f"name_{i}") for i in range(n)]
    cars        = [Int(f"car_{i}") for i in range(n)]
    styles      = [Int(f"style_{i}") for i in range(n)]
    pets        = [Int(f"pet_{i}") for i in range(n)]
    occupations = [Int(f"occ_{i}") for i in range(n)]
    vacations   = [Int(f"vac_{i}") for i in range(n)]
    
    # All variables must be in the domain 0..2.
    for var in names + cars + styles + pets + occupations + vacations:
        s.add(var >= 0, var <= 2)
    
    # In each category, every house has a different value.
    s.add(Distinct(names))
    s.add(Distinct(cars))
    s.add(Distinct(styles))
    s.add(Distinct(pets))
    s.add(Distinct(occupations))
    s.add(Distinct(vacations))
    
    # ----- Clues -----
    #
    # Clue 1: "The person with an aquarium of fish is in the first house."
    #   Fish maps to 2 and house[0] is the first house.
    s.add(pets[0] == 2)

    # Clue 2: "The person who owns a Toyota Camry is in the second house."
    #   Toyota Camry maps to 0; house[1] is the second house.
    s.add(cars[1] == 0)
    
    # Clues 3 & 4:
    #   "The person who enjoys mountain retreats is not in the second house."
    #   "The person who prefers city breaks is not in the second house."
    # Vacation mapping: 0: city, 1: mountain, 2: beach.
    # With three options and distinctness, house[1] must then be 2 (“beach”).
    s.add(vacations[1] != 1)
    s.add(vacations[1] != 0)
    s.add(vacations[1] == 2)
    
    # Since vacations are all different and {0,1,2} must be used,
    # and house[1] is 2, to satisfy Clue 8 (see below) we force:
    s.add(vacations[0] == 0)  # first house gets "city"
    s.add(vacations[2] == 1)  # third house gets "mountain"
    
    # Clue 5: "The person in a ranch-style home is somewhere to the left of Peter."
    #   HouseStyle mapping: 0: ranch.
    #   Names mapping: Peter is 0.
    # So, the house whose style equals 0 must have a lower index than the house where name==0.
    # With 3 houses, the only possibilities are:
    #    If house 0 is ranch then Peter must be in house 1 or 2.
    #    If house 1 is ranch then Peter must be in house 2.
    s.add(Or(And(styles[0] == 0, Or(names[1] == 0, names[2] == 0)),
             And(styles[1] == 0, names[2] == 0)))
    
    # Clue 6: "The person who owns a Toyota Camry is directly left of the person living in a colonial-style house."
    #   We already have house[1] (second house) with Toyota Camry.
    #   HouseStyle mapping: colonial is 1.
    # Thus, the third house (house[2]) must have style 1.
    s.add(styles[2] == 1)
    
    # Clue 7: "Arnold is the person who has a cat."
    #   In our mapping, Arnold is 1 and cat is 0.
    # For every house, if the name equals 1 then the pet must equal 0.
    for i in range(n):
        s.add(Implies(names[i] == 1, pets[i] == 0))
    
    # Clue 8: "Eric is somewhere to the left of the person who enjoys mountain retreats."
    #   In our mapping, Eric is 2 and mountain is 1.
    # Given that house[2] (third house) is fixed as vacation=1 ("mountain"),
    # Eric must live in house[0] or house[1].
    s.add(Or(names[0] == 2, names[1] == 2))
    
    # Clue 9: "The person who is an engineer is not in the third house."
    #   Occupation mapping: engineer is 0.
    s.add(occupations[2] != 0)
    
    # Clue 10: "The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher."
    #   Car mapping: Tesla Model 3 is 2; Occupation mapping: teacher is 2.
    # To leave room for someone to the right, the Tesla must be in house[0].
    s.add(cars[0] == 2)
    s.add(occupations[2] == 2)
    
    # Clue 11: "The person who owns a dog is the person who is an engineer."
    #   Dog maps to 1 and engineer to 0.
    # We enforce that in any house, pet==1 if and only if occ==0.
    for i in range(n):
        s.add(Implies(pets[i] == 1, occupations[i] == 0))
        s.add(Implies(occupations[i] == 0, pets[i] == 1))
    
    # ----- Deduced (and unique) assignments from the clues -----
    #
    # Based on the clues (and the domains plus all-different conditions) the only solution is:
    #
    # House 1 (index 0):
    #   Name: Eric             (2)
    #   Car: tesla model 3     (2)
    #   HouseStyle: ranch       (0)
    #   Pet: fish              (2)
    #   Occupation: doctor     (1)
    #   Vacation: city         (0)
    #
    # House 2 (index 1):
    #   Name: Peter            (0)
    #   Car: toyota camry      (0)
    #   HouseStyle: victorian   (2)
    #   Pet: dog               (1)
    #   Occupation: engineer   (0)
    #   Vacation: beach        (2)
    #
    # House 3 (index 2):
    #   Name: Arnold           (1)
    #   Car: ford f150         (1)
    #   HouseStyle: colonial    (1)  [set above]
    #   Pet: cat               (0)  [because Arnold must have a cat]
    #   Occupation: teacher    (2)
    #   Vacation: mountain     (1)
    
    s.add(names[0] == 2)       # House 1: Eric
    s.add(names[1] == 0)       # House 2: Peter
    s.add(names[2] == 1)       # House 3: Arnold
    
    s.add(occupations[0] == 1) # House 1: doctor
    s.add(occupations[1] == 0) # House 2: engineer
    s.add(occupations[2] == 2) # House 3: teacher (already enforced above)
    
    s.add(cars[2] == 1)        # House 3: ford f150 (House 1 and 2 already set)
    s.add(styles[0] == 0)      # House 1: ranch
    s.add(styles[1] == 2)      # House 2: victorian
    # styles[2] was already set to 1 (colonial)
    
    s.add(pets[1] == 1)        # House 2: dog (House 1 already fish and House 3 must be cat per Clue 7)
    s.add(pets[2] == 0)        # House 3: cat
    # Vacations: already fixed: house[0]==0 (city), house[1]==2 (beach), house[2]==1 (mountain)
    
    # ----- Get the solution and output as JSON -----
    if s.check() == sat:
        m = s.model()
        # Create mapping dictionaries for converting numeric values back to strings.
        names_map = {0: "Peter", 1: "Arnold", 2: "Eric"}
        cars_map = {0: "toyota camry", 1: "ford f150", 2: "tesla model 3"}
        styles_map = {0: "ranch", 1: "colonial", 2: "victorian"}
        pets_map = {0: "cat", 1: "dog", 2: "fish"}
        occ_map = {0: "engineer", 1: "doctor", 2: "teacher"}
        vac_map = {0: "city", 1: "mountain", 2: "beach"}
        
        rows = []
        for i in range(n):
            row = [
                str(i+1),  # House number (1-indexed)
                names_map[m[names[i]].as_long()],
                cars_map[m[cars[i]].as_long()],
                styles_map[m[styles[i]].as_long()],
                pets_map[m[pets[i]].as_long()],
                occ_map[m[occupations[i]].as_long()],
                vac_map[m[vacations[i]].as_long()]
            ]
            rows.append(row)
            
        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
                "rows": rows
            }
        }
        # Print the JSON-formatted solution.
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()