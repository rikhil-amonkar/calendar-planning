import json
from itertools import permutations

def main():
    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]
    
    # Generate all possible permutations for names and children
    for name_perm in permutations(names):
        for child_perm in permutations(children):
            assignment = list(zip(name_perm, child_perm))
            
            # Check clue 3: Fred is in second house
            if assignment[1][1] != "Fred":
                continue
                
            # Check clue 5: Eric not in third house
            if assignment[2][0] == "Eric":
                continue
                
            # Check clue 6: Bob not in third house
            if assignment[2][0] == "Bob":
                continue
                
            # Check clue 7: Fred directly left of Bella
            fred_index = None
            bella_index = None
            for i, (_, child) in enumerate(assignment):
                if child == "Fred":
                    fred_index = i
                if child == "Bella":
                    bella_index = i
            if fred_index is None or bella_index is None or bella_index != fred_index + 1:
                continue
                
            # Check clue 1: Bob left of Samantha's child
            bob_index = None
            samantha_child_index = None
            for i, (name, child) in enumerate(assignment):
                if name == "Bob":
                    bob_index = i
                if child == "Samantha":
                    samantha_child_index = i
            if bob_index is None or samantha_child_index is None or bob_index >= samantha_child_index:
                continue
                
            # Check clue 2: Timothy's mother left of Samantha's child
            timothy_child_index = None
            for i, (_, child) in enumerate(assignment):
                if child == "Timothy":
                    timothy_child_index = i
            if timothy_child_index is None or timothy_child_index >= samantha_child_index:
                continue
                
            # Check clue 4: One house between Alice and Samantha's child
            alice_index = None
            for i, (name, _) in enumerate(assignment):
                if name == "Alice":
                    alice_index = i
            if alice_index is None or abs(alice_index - samantha_child_index) != 2:
                continue
                
            # Check clue 8: Samantha's child left of Peter
            peter_index = None
            for i, (name, _) in enumerate(assignment):
                if name == "Peter":
                    peter_index = i
            if peter_index is None or samantha_child_index >= peter_index:
                continue
                
            # Found valid assignment
            result = {
                "solution": {
                    "header": ["House", "Name", "Children"],
                    "rows": []
                }
            }
            
            for i, (name, child) in enumerate(assignment):
                result["solution"]["rows"].append([str(i+1), name, child])
            
            print(json.dumps(result, indent=2))
            return
    
    print('{"solution": {"header": ["House", "Name", "Children"], "rows": []}}')

if __name__ == "__main__":
    main()