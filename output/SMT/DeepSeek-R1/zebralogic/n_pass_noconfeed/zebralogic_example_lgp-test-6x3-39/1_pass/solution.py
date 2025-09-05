import json
from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Houses
    houses = [1, 2, 3, 4, 5, 6]
    
    # Attributes mappings
    names = {"Arnold": 1, "Peter": 2, "Carol": 3, "Alice": 4, "Bob": 5, "Eric": 6}
    children = {"Alice": 1, "Timothy": 2, "Bella": 3, "Meredith": 4, "Fred": 5, "Samantha": 6}
    smoothies = {"desert": 1, "cherry": 2, "watermelon": 3, "blueberry": 4, "lime": 5, "dragonfruit": 6}
    
    # Reverse mappings for output
    rev_names = {v: k for k, v in names.items()}
    rev_children = {v: k for k, v in children.items()}
    rev_smoothies = {v: k for k, v in smoothies.items()}
    
    # Create integer variables for each attribute per house
    name_vars = [Int(f"name_{i}") for i in houses]
    child_vars = [Int(f"child_{i}") for i in houses]
    smoothie_vars = [Int(f"smoothie_{i}") for i in houses]
    
    # Constraint: All attributes are between 1 and 6
    for i in houses:
        s.add(And(name_vars[i-1] >= 1, name_vars[i-1] <= 6))
        s.add(And(child_vars[i-1] >= 1, child_vars[i-1] <= 6))
        s.add(And(smoothie_vars[i-1] >= 1, smoothie_vars[i-1] <= 6))
    
    # Constraint: All attributes are distinct
    s.add(Distinct(name_vars))
    s.add(Distinct(child_vars))
    s.add(Distinct(smoothie_vars))
    
    # Clue 1: The person's child is named Fred and the Desert smoothie lover are next to each other.
    fred_child = children["Fred"]
    desert_smoothie = smoothies["desert"]
    s.add(Or(
        *[And(child_vars[i] == fred_child, smoothie_vars[i+1] == desert_smoothie) for i in range(5)],
        *[And(child_vars[i+1] == fred_child, smoothie_vars[i] == desert_smoothie) for i in range(5)]
    ))
    
    # Clue 2: The person who drinks Blueberry smoothies is somewhere to the left of the person's child is named Fred.
    blueberry_smoothie = smoothies["blueberry"]
    s.add(Or(
        *[And(smoothie_vars[i] == blueberry_smoothie, 
               Or(*[child_vars[j] == fred_child for j in range(i+1, 6)])) for i in range(5)]
    ))
    
    # Clue 3: Alice is not in the fifth house.
    alice_name = names["Alice"]
    s.add(name_vars[4] != alice_name)
    
    # Clue 4: The person's child is named Samantha is not in the second house.
    samantha_child = children["Samantha"]
    s.add(child_vars[1] != samantha_child)
    
    # Clue 5: The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies.
    watermelon_smoothie = smoothies["watermelon"]
    cherry_smoothie = smoothies["cherry"]
    s.add(Or(
        *[And(smoothie_vars[i] == cherry_smoothie, 
               Or(*[smoothie_vars[j] == watermelon_smoothie for j in range(i+1, 6)])) for i in range(5)]
    ))
    
    # Clue 6: Alice is the person's child is named Alice.
    # This means the person named Alice has child named Alice.
    alice_child = children["Alice"]
    s.add(Or([And(name_vars[i] == alice_name, child_vars[i] == alice_child) for i in range(6)]))
    
    # Clue 7: Alice is the Watermelon smoothie lover.
    s.add(Or([And(name_vars[i] == alice_name, smoothie_vars[i] == watermelon_smoothie) for i in range(6)]))
    
    # Clue 8: Peter is somewhere to the right of the person's child is named Samantha.
    peter_name = names["Peter"]
    s.add(Or(
        *[And(child_vars[i] == samantha_child, 
               Or(*[name_vars[j] == peter_name for j in range(i+1, 6)])) for i in range(5)]
    ))
    
    # Clue 9: Arnold is not in the second house.
    arnold_name = names["Arnold"]
    s.add(name_vars[1] != arnold_name)
    
    # Clue 10: Bob is the person who is the mother of Timothy.
    bob_name = names["Bob"]
    timothy_child = children["Timothy"]
    s.add(Or([And(name_vars[i] == bob_name, child_vars[i] == timothy_child) for i in range(6)]))
    
    # Clue 11: Arnold is directly left of Carol.
    carol_name = names["Carol"]
    s.add(Or([And(name_vars[i] == arnold_name, name_vars[i+1] == carol_name) for i in range(5)]))
    
    # Clue 12: The person who likes Cherry smoothies is directly left of the person's child is named Samantha.
    s.add(Or([And(smoothie_vars[i] == cherry_smoothie, child_vars[i+1] == samantha_child) for i in range(5)]))
    
    # Clue 13: The person's child is named Meredith is in the sixth house.
    meredith_child = children["Meredith"]
    s.add(child_vars[5] == meredith_child)
    
    # Clue 14: The Dragonfruit smoothie lover is the person's child is named Meredith.
    dragonfruit_smoothie = smoothies["dragonfruit"]
    s.add(Or([And(smoothie_vars[i] == dragonfruit_smoothie, child_vars[i] == meredith_child) for i in range(6)]))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        
        # Retrieve values
        name_values = [m.evaluate(name_vars[i]).as_long() for i in range(6)]
        child_values = [m.evaluate(child_vars[i]).as_long() for i in range(6)]
        smoothie_values = [m.evaluate(smoothie_vars[i]).as_long() for i in range(6)]
        
        # Map back to strings
        rows = []
        for i in range(6):
            house_num = str(i+1)
            name_str = rev_names[name_values[i]]
            child_str = rev_children[child_values[i]]
            smoothie_str = rev_smoothies[smoothie_values[i]]
            rows.append([house_num, name_str, child_str, smoothie_str])
        
        # Create solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "Children", "Smoothie"],
                "rows": rows
            }
        }
        
        # Output JSON
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()