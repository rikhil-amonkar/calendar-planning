#!/usr/bin/env python3
import itertools
import json

def main():
    persons = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]
    
    solution = None
    
    # Iterate over all assignments of persons to houses
    for p in itertools.permutations(persons):
        # Clue 5: Eric is not in the third house (index 2)
        # Clue 6: Bob is not in the third house (index 2)
        if p[2] == "Eric" or p[2] == "Bob":
            continue
        
        # Iterate over all assignments of children to houses
        for c in itertools.permutations(children):
            # Clue 3: The person's child is named Fred is in the second house (index 1)
            if c[1] != "Fred":
                continue
            # Clue 7: Fred is directly left of Bella.
            # Since Fred is fixed in house 2 (index 1), Bella must be in house 3 (index 2).
            if c[2] != "Bella":
                continue
            
            # Clue 2: The person who is the mother of Timothy (house with child Timothy)
            # is somewhere to the left of the house with child Samantha.
            idx_timothy = c.index("Timothy")
            idx_samantha = c.index("Samantha")
            if not (idx_timothy < idx_samantha):
                continue
            
            # Clue 1: Bob is somewhere to the left of the house with child Samantha.
            idx_bob = p.index("Bob")
            if not (idx_bob < idx_samantha):
                continue
            
            # Clue 8: The house with child Samantha is somewhere to the left of the house with Peter.
            idx_peter = p.index("Peter")
            if not (idx_samantha < idx_peter):
                continue
            
            # Clue 4: There is one house between Alice and the house with child Samantha.
            idx_alice = p.index("Alice")
            if abs(idx_alice - idx_samantha) != 2:
                continue
            
            # If all constraints are satisfied, we have found the solution.
            solution = {"persons": p, "children": c}
            break
        if solution is not None:
            break

    # Prepare the JSON output in the required format.
    if solution is not None:
        rows = []
        for i in range(5):
            # House numbers are 1-indexed.
            row = [str(i+1), solution["persons"][i], solution["children"][i]]
            rows.append(row)
        output = {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": rows
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": {"header": ["House", "Name", "Children"], "rows": []}}))

if __name__ == "__main__":
    main()