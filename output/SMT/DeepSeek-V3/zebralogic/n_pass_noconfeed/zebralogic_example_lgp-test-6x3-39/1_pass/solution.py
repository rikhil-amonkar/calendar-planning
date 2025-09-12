import z3
import json

def main():
    solver = z3.Solver()
    
    n_houses = 6
    houses = list(range(1, n_houses+1))
    
    # Define the attributes
    names = ['Arnold', 'Peter', 'Carol', 'Alice', 'Bob', 'Eric']
    children = ['Alice', 'Timothy', 'Bella', 'Meredith', 'Fred', 'Samantha']
    smoothies = ['desert', 'cherry', 'watermelon', 'blueberry', 'lime', 'dragonfruit']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f"name_{i}") for i in houses]
    child_vars = [z3.Int(f"child_{i}") for i in houses]
    smoothie_vars = [z3.Int(f"smoothie_{i}") for i in houses]
    
    # Constraint: all attributes are within their respective ranges
    for i in houses:
        solver.add(z3.And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(z3.And(child_vars[i-1] >= 0, child_vars[i-1] < len(children)))
        solver.add(z3.And(smoothie_vars[i-1] >= 0, smoothie_vars[i-1] < len(smoothies)))
    
    # Constraint: all attributes are distinct per category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(child_vars))
    solver.add(z3.Distinct(smoothie_vars))
    
    # Helper function to get the house index of an attribute value
    def get_house_index(vars_list, value):
        return z3.If(vars_list[0] == value, 1, 
            z3.If(vars_list[1] == value, 2,
            z3.If(vars_list[2] == value, 3,
            z3.If(vars_list[3] == value, 4,
            z3.If(vars_list[4] == value, 5, 6)))))
    
    # Helper function for "next to" constraint
    def adjacent(a, b):
        return z3.Or(a == b-1, a == b+1)
    
    # Helper function for "to the left of" constraint
    def left_of(a, b):
        return a < b
    
    # Helper function for "directly left of" constraint
    def directly_left_of(a, b):
        return a == b-1
    
    # Clue 1: The person's child is named Fred and the Desert smoothie lover are next to each other.
    fred_child_house = get_house_index(child_vars, children.index('Fred'))
    desert_smoothie_house = get_house_index(smoothie_vars, smoothies.index('desert'))
    solver.add(adjacent(fred_child_house, desert_smoothie_house))
    
    # Clue 2: The person who drinks Blueberry smoothies is somewhere to the left of the person's child is named Fred.
    blueberry_smoothie_house = get_house_index(smoothie_vars, smoothies.index('blueberry'))
    solver.add(left_of(blueberry_smoothie_house, fred_child_house))
    
    # Clue 3: Alice is not in the fifth house.
    alice_name_house = get_house_index(name_vars, names.index('Alice'))
    solver.add(alice_name_house != 5)
    
    # Clue 4: The person's child is named Samantha is not in the second house.
    samantha_child_house = get_house_index(child_vars, children.index('Samantha'))
    solver.add(samantha_child_house != 2)
    
    # Clue 5: The Watermelon smoothie lover is somewhere to the right of the person who likes Cherry smoothies.
    watermelon_smoothie_house = get_house_index(smoothie_vars, smoothies.index('watermelon'))
    cherry_smoothie_house = get_house_index(smoothie_vars, smoothies.index('cherry'))
    solver.add(left_of(cherry_smoothie_house, watermelon_smoothie_house))
    
    # Clue 6: Alice is the person's child is named Alice.
    alice_child_house = get_house_index(child_vars, children.index('Alice'))
    solver.add(alice_name_house == alice_child_house)
    
    # Clue 7: Alice is the Watermelon smoothie lover.
    solver.add(alice_name_house == watermelon_smoothie_house)
    
    # Clue 8: Peter is somewhere to the right of the person's child is named Samantha.
    peter_name_house = get_house_index(name_vars, names.index('Peter'))
    solver.add(left_of(samantha_child_house, peter_name_house))
    
    # Clue 9: Arnold is not in the second house.
    arnold_name_house = get_house_index(name_vars, names.index('Arnold'))
    solver.add(arnold_name_house != 2)
    
    # Clue 10: Bob is the person who is the mother of Timothy.
    bob_name_house = get_house_index(name_vars, names.index('Bob'))
    timothy_child_house = get_house_index(child_vars, children.index('Timothy'))
    solver.add(bob_name_house == timothy_child_house)
    
    # Clue 11: Arnold is directly left of Carol.
    carol_name_house = get_house_index(name_vars, names.index('Carol'))
    solver.add(directly_left_of(arnold_name_house, carol_name_house))
    
    # Clue 12: The person who likes Cherry smoothies is directly left of the person's child is named Samantha.
    solver.add(directly_left_of(cherry_smoothie_house, samantha_child_house))
    
    # Clue 13: The person's child is named Meredith is in the sixth house.
    meredith_child_house = get_house_index(child_vars, children.index('Meredith'))
    solver.add(meredith_child_house == 6)
    
    # Clue 14: The Dragonfruit smoothie lover is the person's child is named Meredith.
    dragonfruit_smoothie_house = get_house_index(smoothie_vars, smoothies.index('dragonfruit'))
    solver.add(dragonfruit_smoothie_house == meredith_child_house)
    
    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result structure
        result = {
            "solution": {
                "header": ["House", "Name", "Children", "Smoothie"],
                "rows": []
            }
        }
        
        # Extract values from the model
        for house in houses:
            name_idx = model.evaluate(name_vars[house-1]).as_long()
            child_idx = model.evaluate(child_vars[house-1]).as_long()
            smoothie_idx = model.evaluate(smoothie_vars[house-1]).as_long()
            
            row = [
                str(house),
                names[name_idx],
                children[child_idx],
                smoothies[smoothie_idx]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()