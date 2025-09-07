import json
from itertools import permutations

def main():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold']
    vacations = ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach']
    
    # Generate all possible assignments
    for name_perm in permutations(names):
        for vac_perm in permutations(vacations):
            assignment = {}
            for i, house in enumerate(houses):
                assignment[house] = {
                    'name': name_perm[i],
                    'vacation': vac_perm[i]
                }
            
            # Check all constraints
            # Clue 2: Eric is somewhere to the right of Alice
            alice_house = None
            eric_house = None
            for house, attrs in assignment.items():
                if attrs['name'] == 'Alice':
                    alice_house = house
                if attrs['name'] == 'Eric':
                    eric_house = house
            if alice_house is None or eric_house is None or eric_house <= alice_house:
                continue
            
            # Clue 3: Eric is in the second house
            if assignment[2]['name'] != 'Eric':
                continue
            
            # Clue 4: The person who goes on cultural tours is in the third house
            if assignment[3]['vacation'] != 'cultural':
                continue
            
            # Clue 5: Bob is directly left of Arnold
            bob_house = None
            arnold_house = None
            for house, attrs in assignment.items():
                if attrs['name'] == 'Bob':
                    bob_house = house
                if attrs['name'] == 'Arnold':
                    arnold_house = house
            if bob_house is None or arnold_house is None or arnold_house != bob_house + 1:
                continue
            
            # Clue 6: The person who enjoys camping trips is not in the first house
            if assignment[1]['vacation'] == 'camping':
                continue
            
            # Clue 7: The person who goes on cultural tours is Peter
            if assignment[3]['name'] != 'Peter':
                continue
            
            # Clue 8: The person who likes going on cruises is Bob
            for house, attrs in assignment.items():
                if attrs['name'] == 'Bob' and attrs['vacation'] != 'cruise':
                    break
            else:
                # This means Bob was found and has cruise vacation
                pass
            else:
                continue
            
            # Clue 9: The person who prefers city breaks is in the fourth house
            if assignment[4]['vacation'] != 'city':
                continue
            
            # Clue 1: The person who goes on cultural tours is somewhere to the left of the person who loves beach vacations
            cultural_house = None
            beach_house = None
            for house, attrs in assignment.items():
                if attrs['vacation'] == 'cultural':
                    cultural_house = house
                if attrs['vacation'] == 'beach':
                    beach_house = house
            if cultural_house is None or beach_house is None or cultural_house >= beach_house:
                continue
            
            # If we reach here, all constraints are satisfied
            result = {
                "solution": {
                    "header": ["House", "Name", "Vacation"],
                    "rows": []
                }
            }
            
            for house in sorted(assignment.keys()):
                attrs = assignment[house]
                result["solution"]["rows"].append([
                    str(house),
                    attrs['name'],
                    attrs['vacation']
                ])
            
            print(json.dumps(result, indent=2))
            return
    
    print('{"solution": {"header": ["House", "Name", "Vacation"], "rows": []}}')

if __name__ == "__main__":
    main()