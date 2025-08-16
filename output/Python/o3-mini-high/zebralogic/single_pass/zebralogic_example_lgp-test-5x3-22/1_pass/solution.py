#!/usr/bin/env python3
import itertools
import json

def solve_zebra():
    # Define the attributes.
    houses = [1, 2, 3, 4, 5]  # House numbers (for clarity)
    names = ["Arnold", "Eric", "Bob", "Peter", "Alice"]
    smoothies = ["desert", "watermelon", "lime", "cherry", "dragonfruit"]
    nationalities = ["german", "swede", "norwegian", "dane", "brit"]
    
    # We'll generate permutations for each attribute list subject to fixed constraints.
    # Fixed constraints:
    # 1. Alice must be in the third house => names[2] == "Alice"
    #    and Peter is not in the first house => names[0] != "Peter"
    # 2. Dragonfruit smoothie is in the second house => smoothies[1] == "dragonfruit"
    #    and Watermelon smoothie is in the third house => smoothies[2] == "watermelon"
    #    and Desert smoothie is not in the fifth house => smoothies[4] != "desert"
    # 3. Norwegian is in the third house and Alice is Norwegian => nationalities[2] == "norwegian"
    #    and the Swedish person is somewhere to the left of the Dragonfruit lover.
    #    Since Dragonfruit is in house two, the only possibility is Swedish in house one => nationalities[0] == "swede"
    
    solutions = []
    
    for perm_names in itertools.permutations(names):
        if perm_names[2] != "Alice":
            continue
        if perm_names[0] == "Peter":
            continue
        
        for perm_smoothies in itertools.permutations(smoothies):
            if perm_smoothies[1] != "dragonfruit":
                continue
            if perm_smoothies[2] != "watermelon":
                continue
            if perm_smoothies[4] == "desert":
                continue
            
            for perm_nationalities in itertools.permutations(nationalities):
                if perm_nationalities[0] != "swede":
                    continue
                if perm_nationalities[2] != "norwegian":
                    continue
                
                # Constraint 1: The Dragonfruit smoothie (house2: index 1) is to the left of Eric.
                if perm_names.index("Eric") <= 1:
                    continue
                
                # Constraint 4: The Dane and the British person are next to each other.
                if abs(perm_nationalities.index("dane") - perm_nationalities.index("brit")) != 1:
                    continue
                
                # Constraint 8: Bob is the Dane.
                index_bob = perm_names.index("Bob")
                if perm_nationalities[index_bob] != "dane":
                    continue
                
                # Constraint 7: There are two houses between the person who drinks Lime smoothies and the Dane (Bob).
                index_lime = perm_smoothies.index("lime")
                if abs(index_lime - index_bob) != 3:
                    continue
                
                # Constraint 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
                # Since Swedish must be house1 (index 0) and Dragonfruit is in house2 (index 1), this is already satisfied.
                
                # All constraints satisfied; construct the solution.
                solution_rows = []
                for i in range(5):
                    # House numbers are expected as strings.
                    solution_rows.append([str(i+1), perm_names[i], perm_smoothies[i], perm_nationalities[i]])
                solutions.append(solution_rows)
                
    return solutions

def main():
    sols = solve_zebra()
    if sols:
        # Take the first valid solution.
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": sols[0]
            }
        }
    else:
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Nationality"],
                "rows": []
            }
        }
    print(json.dumps(solution, indent=2))

if __name__ == '__main__':
    main()