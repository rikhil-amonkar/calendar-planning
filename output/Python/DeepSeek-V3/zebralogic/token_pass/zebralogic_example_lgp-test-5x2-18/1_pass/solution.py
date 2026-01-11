import json
from itertools import permutations

def solve():
    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    children = ["Timothy", "Meredith", "Samantha", "Fred", "Bella"]
    houses = [1, 2, 3, 4, 5]

    # Generate all possible permutations for names and children
    for name_perm in permutations(names, 5):
        for child_perm in permutations(children, 5):
            # Create assignment dictionaries
            assignment = {}
            for i in range(5):
                assignment[houses[i]] = {
                    'name': name_perm[i],
                    'child': child_perm[i]
                }

            # Clue 3: Fred is in the second house
            if assignment[2]['child'] != 'Fred':
                continue

            # Clue 7: Fred is directly left of Bella
            if assignment[3]['child'] != 'Bella':
                continue

            # Clue 1: Bob is somewhere to the left of Samantha's parent
            bob_house = None
            samantha_house = None
            for h in houses:
                if assignment[h]['name'] == 'Bob':
                    bob_house = h
                if assignment[h]['child'] == 'Samantha':
                    samantha_house = h
            if bob_house is None or samantha_house is None:
                continue
            if not (bob_house < samantha_house):
                continue

            # Clue 2: Timothy's parent is somewhere to the left of Samantha's parent
            timothy_house = None
            for h in houses:
                if assignment[h]['child'] == 'Timothy':
                    timothy_house = h
            if timothy_house is None:
                continue
            if not (timothy_house < samantha_house):
                continue

            # Clue 4: One house between Alice and Samantha's parent
            alice_house = None
            for h in houses:
                if assignment[h]['name'] == 'Alice':
                    alice_house = h
            if alice_house is None:
                continue
            if abs(alice_house - samantha_house) != 2:
                continue

            # Clue 5: Eric is not in the third house
            if assignment[3]['name'] == 'Eric':
                continue

            # Clue 6: Bob is not in the third house
            if assignment[3]['name'] == 'Bob':
                continue

            # Clue 8: Samantha's parent is somewhere to the left of Peter
            peter_house = None
            for h in houses:
                if assignment[h]['name'] == 'Peter':
                    peter_house = h
            if peter_house is None:
                continue
            if not (samantha_house < peter_house):
                continue

            # All clues satisfied, construct solution
            rows = []
            for h in houses:
                rows.append([str(h), assignment[h]['name'], assignment[h]['child']])
            
            return {
                "solution": {
                    "header": ["House", "Name", "Children"],
                    "rows": rows
                }
            }
    
    return {"solution": {"header": ["House", "Name", "Children"], "rows": []}}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))