import json
from itertools import permutations

def solve():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Bob", "Peter", "Alice", "Eric", "Carol", "Arnold"]
    vacations = ["mountain", "camping", "cruise", "city", "cultural", "beach"]
    
    # Generate all possible permutations of names and vacations
    for name_perm in permutations(names, 6):
        for vac_perm in permutations(vacations, 6):
            # Create assignment dictionaries
            assignment = {}
            for i in range(6):
                assignment[houses[i]] = {
                    'name': name_perm[i],
                    'vacation': vac_perm[i]
                }
            
            # Clue 2: Eric is somewhere to the right of Alice
            eric_house = None
            alice_house = None
            for h in houses:
                if assignment[h]['name'] == 'Eric':
                    eric_house = h
                if assignment[h]['name'] == 'Alice':
                    alice_house = h
            if not (eric_house and alice_house and eric_house > alice_house):
                continue
            
            # Clue 3: Eric is in the second house
            if eric_house != 2:
                continue
            
            # Clue 4: The person who goes on cultural tours is in the third house
            if assignment[3]['vacation'] != 'cultural':
                continue
            
            # Clue 5: Bob is directly left of Arnold
            bob_house = None
            arnold_house = None
            for h in houses:
                if assignment[h]['name'] == 'Bob':
                    bob_house = h
                if assignment[h]['name'] == 'Arnold':
                    arnold_house = h
            if not (bob_house and arnold_house and arnold_house == bob_house + 1):
                continue
            
            # Clue 6: The person who enjoys camping trips is not in the first house
            if assignment[1]['vacation'] == 'camping':
                continue
            
            # Clue 7: The person who goes on cultural tours is Peter
            if assignment[3]['name'] != 'Peter':
                continue
            
            # Clue 8: The person who likes going on cruises is Bob
            bob_vac_house = None
            for h in houses:
                if assignment[h]['name'] == 'Bob':
                    bob_vac_house = h
            if assignment[bob_vac_house]['vacation'] != 'cruise':
                continue
            
            # Clue 9: The person who prefers city breaks is in the fourth house
            if assignment[4]['vacation'] != 'city':
                continue
            
            # Clue 1: The person who goes on cultural tours is somewhere to the left of the person who loves beach vacations
            cultural_house = 3  # From clue 4
            beach_house = None
            for h in houses:
                if assignment[h]['vacation'] == 'beach':
                    beach_house = h
            if not (beach_house and cultural_house < beach_house):
                continue
            
            # All constraints satisfied - build solution
            rows = []
            for h in houses:
                rows.append([str(h), assignment[h]['name'], assignment[h]['vacation']])
            
            return {
                "solution": {
                    "header": ["House", "Name", "Vacation"],
                    "rows": rows
                }
            }
    
    return None

if __name__ == "__main__":
    solution = solve()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))