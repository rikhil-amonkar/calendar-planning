from z3 import *
import json

def solve_puzzle():
    s = Solver()
    houses = 3

    # Create Z3 integer arrays for each attribute.
    # Their possible values are 0, 1, 2 which will be mapped to actual strings.
    name = [Int(f"name_{i}") for i in range(houses)]
    vacation = [Int(f"vacation_{i}") for i in range(houses)]
    height = [Int(f"height_{i}") for i in range(houses)]
    flower = [Int(f"flower_{i}") for i in range(houses)]
    hair = [Int(f"hair_{i}") for i in range(houses)]
    education = [Int(f"education_{i}") for i in range(houses)]
    
    variables = name + vacation + height + flower + hair + education
    for var in variables:
        s.add(var >= 0, var <= 2)
    
    # The puzzles demands that in each category all values are unique.
    s.add(Distinct(name))
    s.add(Distinct(vacation))
    s.add(Distinct(height))
    s.add(Distinct(flower))
    s.add(Distinct(hair))
    s.add(Distinct(education))
    
    # We use the following mappings:
    # Name: 0 -> "Eric",    1 -> "Arnold",  2 -> "Peter"
    # Vacation: 0 -> "beach", 1 -> "city",    2 -> "mountain"
    # Height: 0 -> "very short", 1 -> "average", 2 -> "short"
    # Flower: 0 -> "lilies",  1 -> "daffodils", 2 -> "carnations"
    # HairColor: 0 -> "brown", 1 -> "black", 2 -> "blonde"
    # Education: 0 -> "bachelor", 1 -> "associate", 2 -> "high school"
    
    # Clue 4: "The person who loves beach vacations is in the first house."
    s.add(vacation[0] == 0)  # 0 means "beach"

    # Clue 11: "The person who loves beach vacations is the person who has brown hair."
    for i in range(houses):
        s.add(Implies(vacation[i] == 0, hair[i] == 0))  # brown hair is 0

    # Clue 10: "The person who has blonde hair is in the third house."
    s.add(hair[2] == 2)  # blonde is 2

    # Clue 5: "The person with a high school diploma is in the third house."
    s.add(education[2] == 2)  # high school is 2

    # Clue 1: "Peter is the person who has an average height."
    for i in range(houses):
        s.add(Implies(name[i] == 2, height[i] == 1))  # Peter (2) => average (1)

    # Clue 2: "The person who loves a bouquet of daffodils is Arnold."
    # We enforce a bidirectional link: a house whose flower is daffodils (1) must have Arnold (1)
    # and Arnold must have daffodils.
    for i in range(houses):
        s.add(Implies(flower[i] == 1, name[i] == 1))
        s.add(Implies(name[i] == 1, flower[i] == 1))

    # Clue 7: "The person who loves the bouquet of lilies is Eric."
    # Similarly, enforce that lilies (0) are linked to Eric (0)
    for i in range(houses):
        s.add(Implies(flower[i] == 0, name[i] == 0))
        s.add(Implies(name[i] == 0, flower[i] == 0))

    # Clue 8: "The person who loves the bouquet of lilies is the person with a bachelor's degree."
    for i in range(houses):
        s.add(Implies(flower[i] == 0, education[i] == 0))  # bachelor's is 0

    # Clue 3: "The person who is very short is not in the second house."
    s.add(height[1] != 0)  # house2 (index 1) cannot be "very short" (0)

    # Clue 6: "The person who is short is somewhere to the right of the person who is very short."
    # Since the heights are all different, we enforce that the unique house with height 0 (very short)
    # must come before the unique house with height 2 (short).
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(height[i] == 0, height[j] == 2), i < j))
    
    # Clue 9: "The person who prefers city breaks is somewhere to the right of Peter."
    for i in range(houses):
        for j in range(houses):
            s.add(Implies(And(name[i] == 2, vacation[j] == 1), i < j))
    
    # At this point, the remaining values will fall into place by the DISTINCT constraints.
    # For instance, by elimination:
    #    • House with name==0 (Eric) will then also have flower==0 => lilies and bachelor's degree (0).
    #    • House with name==1 (Arnold) will have flower==1 => daffodils.
    #    • The remaining house gets name==2 (Peter) and by Clue 1 must have average height (1).
    # Similarly, vacations:
    #    • House1 is beach (0).
    #    • By Clue 9 the house with vacation==1 (city) must be to the right of Peter,
    #      and the only possibility then is the third house gets city (1) and the second house gets mountain (2).
    #
    # Now solve the model.
    if s.check() == sat:
        m = s.model()
        # Mapping dictionaries to convert number to string labels.
        name_map = {0: "Eric", 1: "Arnold", 2: "Peter"}
        vacation_map = {0: "beach", 1: "city", 2: "mountain"}
        height_map = {0: "very short", 1: "average", 2: "short"}
        flower_map = {0: "lilies", 1: "daffodils", 2: "carnations"}
        hair_map = {0: "brown", 1: "black", 2: "blonde"}
        education_map = {0: "bachelor", 1: "associate", 2: "high school"}
        
        solution_rows = []
        for i in range(houses):
            row = [
                str(i+1),
                name_map[m.evaluate(name[i]).as_long()],
                vacation_map[m.evaluate(vacation[i]).as_long()],
                height_map[m.evaluate(height[i]).as_long()],
                flower_map[m.evaluate(flower[i]).as_long()],
                hair_map[m.evaluate(hair[i]).as_long()],
                education_map[m.evaluate(education[i]).as_long()]
            ]
            solution_rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    solve_puzzle()