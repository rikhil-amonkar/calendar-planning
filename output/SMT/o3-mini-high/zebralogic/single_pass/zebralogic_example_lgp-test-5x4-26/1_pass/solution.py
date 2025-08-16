from z3 import *
import json

def main():
    houses = 5
    solver = Solver()

    # Create one integer variable per attribute per house.
    names   = [Int("name_%d" % i)   for i in range(houses)]
    heights = [Int("height_%d" % i) for i in range(houses)]
    mothers = [Int("mother_%d" % i) for i in range(houses)]
    hairs   = [Int("hair_%d" % i)   for i in range(houses)]
    
    # Each variable is between 1 and 5.
    for var in names + heights + mothers + hairs:
        solver.add(var >= 1, var <= houses)
    
    # All attributes are all-different across houses.
    solver.add(Distinct(names))
    solver.add(Distinct(heights))
    solver.add(Distinct(mothers))
    solver.add(Distinct(hairs))
    
    # We use the following mappings:
    # Names:    1:"Alice", 2:"Peter", 3:"Bob", 4:"Eric", 5:"Arnold"
    # Heights:  1:"very short", 2:"short", 3:"tall", 4:"average", 5:"very tall"
    # Mothers:  1:"Janelle", 2:"Kailyn", 3:"Penny", 4:"Holly", 5:"Aniya"
    # Hairs:    1:"blonde", 2:"black", 3:"gray", 4:"red", 5:"brown"

    # Clue 1: The person who is tall (3) is the person whose mother's name is Holly (4).
    for i in range(houses):
        solver.add(Implies(heights[i] == 3, mothers[i] == 4))
        solver.add(Implies(mothers[i] == 4, heights[i] == 3))
    
    # Clue 6: The person who is very short (1) is the person whose mother's name is Penny (3).
    for i in range(houses):
        solver.add(Implies(heights[i] == 1, mothers[i] == 3))
        solver.add(Implies(mothers[i] == 3, heights[i] == 1))
    
    # Clue 5: Eric (4) is the person who has black hair (2).
    for i in range(houses):
        solver.add(Implies(names[i] == 4, hairs[i] == 2))
        solver.add(Implies(hairs[i] == 2, names[i] == 4))
    
    # Clue 9: The person who has red hair (4) is Peter (2).
    for i in range(houses):
        solver.add(Implies(names[i] == 2, hairs[i] == 4))
        solver.add(Implies(hairs[i] == 4, names[i] == 2))
    
    # Clue 11: Arnold (5) is the person who has brown hair (5).
    for i in range(houses):
        solver.add(Implies(names[i] == 5, hairs[i] == 5))
        solver.add(Implies(hairs[i] == 5, names[i] == 5))
    
    # Clue 14: The person whose mother's name is Kailyn (2) is in the third house.
    solver.add(mothers[2] == 2)
    
    # Clue 8: Bob (3) is in the fifth house.
    solver.add(names[4] == 3)
    
    # Clue 10: The person whose mother's name is Kailyn (2) is directly left of the person who is short (2).
    for i in range(houses - 1):
        solver.add(Implies(mothers[i] == 2, heights[i+1] == 2))
    for i in range(1, houses):
        solver.add(Implies(heights[i] == 2, mothers[i-1] == 2))
    
    # Clue 7: Eric and the person who has gray hair (3) are next to each other.
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(names[i] == 4, hairs[j] == 3), Or(i == j+1, i == j-1)))
    
    # Clue 3: The person who has gray hair (3) is directly left of the person whose mother's name is Janelle (1).
    for i in range(houses - 1):
        solver.add(Implies(hairs[i] == 3, mothers[i+1] == 1))
    for i in range(1, houses):
        solver.add(Implies(mothers[i] == 1, hairs[i-1] == 3))
    
    # Clue 12: The person who has brown hair (5) is somewhere to the left of the person whose mother's name is Janelle (1).
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(hairs[i] == 5, mothers[j] == 1), i < j))
    
    # Clue 2: There are two houses between the person who has an average height (4) and the person who is short (2).
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(heights[i] == 4, heights[j] == 2), Abs(i - j) == 3))
    
    # Clue 13: The person whose mother's name is Aniya (5) and the person who is very short (1) are next to each other.
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(mothers[i] == 5, heights[j] == 1), Or(i == j+1, i == j-1)))
    
    # Clue 4: The person who has black hair (2) is not in the fourth house.
    solver.add(hairs[3] != 2)
    
    # (Domain and distinct constraints plus the above ensure a unique assignment for each house.)
    
    if solver.check() == sat:
        model = solver.model()
        # Decoding using our mappings:
        name_map   = {1: "Alice", 2: "Peter", 3: "Bob", 4: "Eric", 5: "Arnold"}
        height_map = {1: "very short", 2: "short", 3: "tall", 4: "average", 5: "very tall"}
        mother_map = {1: "Janelle", 2: "Kailyn", 3: "Penny", 4: "Holly", 5: "Aniya"}
        hair_map   = {1: "blonde", 2: "black", 3: "gray", 4: "red", 5: "brown"}
        
        solution_rows = []
        for i in range(houses):
            house = str(i + 1)
            sol_name   = name_map[model[names[i]].as_long()]
            sol_height = height_map[model[heights[i]].as_long()]
            sol_mother = mother_map[model[mothers[i]].as_long()]
            sol_hair   = hair_map[model[hairs[i]].as_long()]
            solution_rows.append([house, sol_name, sol_height, sol_mother, sol_hair])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Height", "Mother", "HairColor"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()