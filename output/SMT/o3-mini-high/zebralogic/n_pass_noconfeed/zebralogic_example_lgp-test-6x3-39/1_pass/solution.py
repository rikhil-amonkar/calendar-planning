from z3 import *
import json

def main():
    houses = 6
    # Create Z3 Int variables for each house attribute.
    names = [Int("name_%d" % i) for i in range(houses)]
    children = [Int("child_%d" % i) for i in range(houses)]
    smoothies = [Int("smoothie_%d" % i) for i in range(houses)]
    
    solver = Solver()
    
    # Each variable must be in the domain 0..5 (6 distinct values)
    for i in range(houses):
        solver.add(And(names[i] >= 0, names[i] < 6))
        solver.add(And(children[i] >= 0, children[i] < 6))
        solver.add(And(smoothies[i] >= 0, smoothies[i] < 6))
        
    # All attributes in each category are distinct.
    solver.add(Distinct(names))
    solver.add(Distinct(children))
    solver.add(Distinct(smoothies))
    
    # Mapping lists for output
    name_map = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    child_map = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    smoothie_map = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]
    
    # -------------------------------
    # Add constraints based on the clues:
    #
    # Clue 1: The person whose child is named Fred (child code 4)
    #         and the Desert smoothie lover (smoothie code 0) are next to each other.
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(children[i] == 4, smoothies[j] == 0),
                                Or(j == i + 1, j == i - 1)))
    
    # Clue 2: The person who drinks Blueberry smoothies (smoothie code 3)
    #         is somewhere to the left of the person whose child is named Fred.
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(smoothies[i] == 3, children[j] == 4), i < j))
    
    # Clue 3: Alice (name code 3) is not in the fifth house (house index 4).
    solver.add(names[4] != 3)
    
    # Clue 4: The person whose child is named Samantha (child code 5) is not in the second house (house index 1).
    solver.add(children[1] != 5)
    
    # Clue 5: The Watermelon smoothie lover (smoothie code 2) is somewhere to the right 
    #         of the person who likes Cherry smoothies (smoothie code 1).
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(smoothies[i] == 1, smoothies[j] == 2), i < j))
    
    # Clue 6: The person named Alice (name code 3) has a child named Alice (child code 0).
    for i in range(houses):
        solver.add(Implies(names[i] == 3, children[i] == 0))
    
    # Clue 7: Alice (name code 3) is the Watermelon smoothie lover (smoothie code 2).
    for i in range(houses):
        solver.add(Implies(names[i] == 3, smoothies[i] == 2))
    
    # Clue 8: Peter (name code 1) is somewhere to the right
    #         of the person whose child is named Samantha (child code 5).
    for i in range(houses):
        for j in range(houses):
            solver.add(Implies(And(names[i] == 1, children[j] == 5), i > j))
    
    # Clue 9: Arnold (name code 0) is not in the second house (house index 1).
    solver.add(names[1] != 0)
    
    # Clue 10: Bob (name code 4) is the mother of Timothy (child code 1).
    for i in range(houses):
        solver.add(Implies(names[i] == 4, children[i] == 1))
    
    # Clue 11: Arnold (name code 0) is directly left of Carol (name code 2).
    for i in range(houses - 1):
        solver.add(Implies(names[i] == 0, names[i + 1] == 2))
    
    # Clue 12: The person who likes Cherry smoothies (smoothie code 1)
    #         is directly left of the person whose child is named Samantha (child code 5).
    for i in range(houses - 1):
        solver.add(Implies(smoothies[i] == 1, children[i + 1] == 5))
    
    # Clue 13: The house in the sixth position (house index 5) has child Meredith (child code 3).
    solver.add(children[5] == 3)
    
    # Clue 14: The Dragonfruit smoothie lover (smoothie code 5)
    #         is the person whose child is named Meredith (child code 3).
    for i in range(houses):
        solver.add(Implies(smoothies[i] == 5, children[i] == 3))
    
    # -------------------------------
    # Solve and output the result as specified.
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Children", "Smoothie"],
                "rows": []
            }
        }
        for i in range(houses):
            house_number = str(i + 1)
            name_val = model[names[i]].as_long()
            child_val = model[children[i]].as_long()
            smoothie_val = model[smoothies[i]].as_long()
            solution["solution"]["rows"].append([
                house_number,
                name_map[name_val],
                child_map[child_val],
                smoothie_map[smoothie_val]
            ])
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == '__main__':
    main()