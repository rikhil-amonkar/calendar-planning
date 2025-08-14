#!/usr/bin/env python3
import itertools
import json

def main():
    # There are 5 houses indexed 0 to 4 corresponding to House 1 to House 5.
    # Attributes:
    # Names: Peter, Alice, Bob, Eric, Arnold. Constraint: Alice must be in house 4 (index 3).
    # Heights: very tall, average, tall, very short, short.
    # Fixed constraints:
    # 1. The person who is short is in the second house (index 1).
    # 7. The person who has an average height is in the fifth house (index 4).
    # 5. Alice is directly left of the person who has an average height.
    #    -> Since average is in house 5 (index 4), house 4 (index 3) must be Alice.
    
    # We'll assign names for houses at indices 0,1,2,4 from the list below and fix index 3 as "Alice".
    names_to_assign = ["Peter", "Bob", "Eric", "Arnold"]
    # We'll assign heights for houses at indices 0,2,3 from the remaining heights.
    heights_to_assign = ["very tall", "tall", "very short"]
    
    solutions = []
    
    for names_perm in itertools.permutations(names_to_assign):
        # Build complete names list for 5 houses.
        # House positions (0-indexed): 0,1,2,3,4.
        names = [None] * 5
        names[0] = names_perm[0]
        names[1] = names_perm[1]
        names[2] = names_perm[2]
        names[3] = "Alice"  # Fixed by clue 5.
        names[4] = names_perm[3]
        
        for heights_perm in itertools.permutations(heights_to_assign):
            # Build complete heights list.
            heights = [None] * 5
            heights[0] = heights_perm[0]
            heights[1] = "short"    # Clue 1: House 2 is short.
            heights[2] = heights_perm[1]
            heights[3] = heights_perm[2]
            heights[4] = "average"  # Clue 7: House 5 is average.
            
            # Clue 6: The person who is short and the person who is very short are next to each other.
            # House 2 (index 1) is short, so very short must be in house 1 (index 0) or house 3 (index 2).
            if not (heights[0] == "very short" or heights[2] == "very short"):
                continue

            # Build a list of houses as dictionaries.
            houses = []
            for i in range(5):
                houses.append({
                    "House": str(i + 1),
                    "Name": names[i],
                    "Height": heights[i]
                })
            
            # Clue 2: Peter is directly left of Bob.
            try:
                peter_index = names.index("Peter")
            except ValueError:
                continue
            if peter_index == 4 or names[peter_index + 1] != "Bob":
                continue

            # Clue 3: Eric is somewhere to the left of Peter.
            try:
                eric_index = names.index("Eric")
            except ValueError:
                continue
            if eric_index >= peter_index:
                continue

            # Clue 4: The person who is very tall is directly left of Peter.
            if peter_index == 0 or heights[peter_index - 1] != "very tall":
                continue

            # Clue 5 is already enforced by fixing Alice in house 4 and clue 7 by fixing average in house 5.
            
            # If all constraints are satisfied, we record the solution.
            solutions.append(houses)
    
    # Output the first found solution in the required JSON format.
    if solutions:
        solution = solutions[0]
        output = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": [[house["House"], house["Name"], house["Height"]] for house in solution]
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()