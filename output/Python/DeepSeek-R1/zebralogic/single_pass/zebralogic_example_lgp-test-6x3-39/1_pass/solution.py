import itertools
import json

def main():
    all_names = ["Arnold", "Peter", "Carol", "Alice", "Bob", "Eric"]
    all_children = ["Alice", "Timothy", "Bella", "Meredith", "Fred", "Samantha"]
    all_smoothies = ["desert", "cherry", "watermelon", "blueberry", "lime", "dragonfruit"]
    
    # We'll try each possible house for Alice (not house5, index4; and not house6, index5 because house6 child is fixed to Meredith)
    for a_house in [0, 1, 2, 3]:
        names = [None] * 6
        children = [None] * 6
        smoothies = [None] * 6
        
        # Set fixed Alice house
        names[a_house] = "Alice"
        children[a_house] = "Alice"
        smoothies[a_house] = "watermelon"
        
        # Set fixed house6 (index5)
        children[5] = "Meredith"
        smoothies[5] = "dragonfruit"
        
        # Free houses for names: all houses except a_house (5 houses)
        free_houses_names = [i for i in range(6) if i != a_house]
        remaining_names = [n for n in all_names if n != "Alice"]
        
        # Free houses for children and smoothies: houses that are not a_house and not 5 (4 houses)
        free_houses_children = [i for i in range(6) if i != a_house and i != 5]
        remaining_children = [c for c in all_children if c != "Alice" and c != "Meredith"]
        
        free_houses_smoothies = free_houses_children[:]  # same houses
        remaining_smoothies = [s for s in all_smoothies if s != "watermelon" and s != "dragonfruit"]
        
        # Generate all permutations for the remaining names
        for name_perm in itertools.permutations(remaining_names):
            for idx, house in enumerate(free_houses_names):
                names[house] = name_perm[idx]
            
            # Generate all permutations for the remaining children
            for child_perm in itertools.permutations(remaining_children):
                for idx, house in enumerate(free_houses_children):
                    children[house] = child_perm[idx]
                
                # Generate all permutations for the remaining smoothies
                for smoothie_perm in itertools.permutations(remaining_smoothies):
                    for idx, house in enumerate(free_houses_smoothies):
                        smoothies[house] = smoothie_perm[idx]
                    
                    # Check all constraints
                    if check_constraints(names, children, smoothies, a_house):
                        # Format the solution
                        solution = {
                            "header": ["House", "Name", "Children", "Smoothie"],
                            "rows": []
                        }
                        for i in range(6):
                            row = [str(i+1), names[i], children[i], smoothies[i]]
                            solution["rows"].append(row)
                        
                        result = {"solution": solution}
                        print(json.dumps(result))
                        return

    # If no solution found, output an empty solution
    result = {
        "solution": {
            "header": ["House", "Name", "Children", "Smoothie"],
            "rows": []
        }
    }
    print(json.dumps(result))

def check_constraints(names, children, smoothies, a_house):
    # Clue1: Child Fred and desert smoothie are next to each other.
    fred_house = None
    for i in range(6):
        if children[i] == "Fred":
            fred_house = i
            break
    if fred_house is None:
        return False
        
    desert_house = None
    for i in range(6):
        if smoothies[i] == "desert":
            desert_house = i
            break
    if desert_house is None:
        return False
        
    if abs(fred_house - desert_house) != 1:
        return False
        
    # Clue2: Blueberry smoothie is left of child Fred.
    blueberry_house = None
    for i in range(6):
        if smoothies[i] == "blueberry":
            blueberry_house = i
            break
    if blueberry_house is None:
        return False
    if blueberry_house >= fred_house:
        return False
        
    # Clue4: Child Samantha is not in house2 (index1).
    if children[1] == "Samantha":
        return False
        
    # Clue5: Watermelon (at a_house) is right of Cherry.
    cherry_house = None
    for i in range(6):
        if smoothies[i] == "cherry":
            cherry_house = i
            break
    if cherry_house is None:
        return False
    if cherry_house >= a_house:
        return False
        
    # Clue8: Peter is right of child Samantha.
    samantha_house = None
    for i in range(6):
        if children[i] == "Samantha":
            samantha_house = i
            break
    if samantha_house is None:
        return False
        
    peter_house = None
    for i in range(6):
        if names[i] == "Peter":
            peter_house = i
            break
    if peter_house is None:
        return False
    if peter_house <= samantha_house:
        return False
        
    # Clue9: Arnold not in house2 (index1).
    if names[1] == "Arnold":
        return False
        
    # Clue10: Bob is mother of Timothy.
    found_bob = False
    for i in range(6):
        if names[i] == "Bob" and children[i] == "Timothy":
            found_bob = True
            break
    if not found_bob:
        return False
        
    # Clue11: Arnold directly left of Carol.
    found_arnold_carol = False
    for i in range(5):
        if names[i] == "Arnold" and names[i+1] == "Carol":
            found_arnold_carol = True
            break
    if not found_arnold_carol:
        return False
        
    # Clue12: Cherry smoothie directly left of child Samantha.
    if cherry_house == 5:
        return False
    if children[cherry_house+1] != "Samantha":
        return False
        
    return True

if __name__ == "__main__":
    main()