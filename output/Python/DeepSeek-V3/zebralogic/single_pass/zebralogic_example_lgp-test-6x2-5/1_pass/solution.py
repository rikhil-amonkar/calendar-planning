import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each attribute
    names = ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold']
    vacations = ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach']
    
    # Initialize houses
    houses = [{'House': str(i+1)} for i in range(6)]
    
    # Apply clue 3: Eric is in the second house
    houses[1]['Name'] = 'Eric'
    
    # Apply clue 4: cultural is in the third house
    houses[2]['Vacation'] = 'cultural'
    
    # Apply clue 7: Peter is in the cultural house (house 3)
    houses[2]['Name'] = 'Peter'
    
    # Apply clue 2: Eric is right of Alice, so Alice must be left of house 2
    # So Alice is in house 1
    houses[0]['Name'] = 'Alice'
    
    # Apply clue 5: Bob is directly left of Arnold
    # Possible positions for Bob and Arnold:
    # Bob in 3, Arnold in 4 - but 3 is Peter
    # Bob in 4, Arnold in 5
    # Bob in 5, Arnold in 6
    # So possible pairs: (4,5) or (5,6)
    
    # Apply clue 8: Bob likes cruise
    # So in whichever house Bob is, vacation is cruise
    
    # Apply clue 9: city is in house 4
    houses[3]['Vacation'] = 'city'
    
    # So Bob cannot be in 4 because vacation is city, not cruise
    # So Bob must be in 5, Arnold in 6
    houses[4]['Name'] = 'Bob'
    houses[5]['Name'] = 'Arnold'
    houses[4]['Vacation'] = 'cruise'
    
    # Remaining names: Carol
    # Only house 3 is Peter, 0 Alice, 1 Eric, 4 Bob, 5 Arnold, so Carol must be in house 3?
    # Wait, house 3 is Peter, so Carol must be placed elsewhere
    # Wait, let's see assigned names:
    # 0: Alice, 1: Eric, 2: Peter, 4: Bob, 5: Arnold
    # So Carol must be in house 3? But house 3 is Peter. Contradiction?
    # Wait, no, house 2 is Peter (since house numbers are 0-based in code but 1-based in puzzle)
    # So in our code:
    # 0: Alice, 1: Eric, 2: Peter, 4: Bob, 5: Arnold
    # So Carol must be in house 3 (index 3)
    houses[3]['Name'] = 'Carol'
    
    # Now assign vacations
    # Assigned vacations:
    # 2: cultural, 3: city, 4: cruise
    # From clue 1: cultural is left of beach, so beach must be right of house 2
    # Possible houses for beach: 3,4,5
    # But 3 is city, 4 is cruise, so beach must be 5
    houses[5]['Vacation'] = 'beach'
    
    # From clue 6: camping is not in first house
    # Remaining vacations: mountain, camping
    # Remaining houses: 0,1
    # Assign to 0 and 1, with camping not in 0
    # So:
    houses[0]['Vacation'] = 'mountain'
    houses[1]['Vacation'] = 'camping'
    
    # Verify all constraints
    # Clue 1: cultural (2) left of beach (5) - yes
    # Clue 2: Eric right of Alice - Alice 0, Eric 1 - yes
    # Clue 3: Eric in second house - yes
    # Clue 4: cultural in third house - yes
    # Clue 5: Bob directly left of Arnold - Bob 4, Arnold 5 - yes
    # Clue 6: camping not in first - camping in 1 - yes
    # Clue 7: cultural is Peter - yes
    # Clue 8: cruise is Bob - yes
    # Clue 9: city in fourth house - yes
    
    # Prepare the solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": []
        }
    }
    
    for house in houses:
        row = [
            house['House'],
            house.get('Name', ''),
            house.get('Vacation', '')
        ]
        solution["solution"]["rows"].append(row)
    
    return json.dumps(solution, indent=2)

if __name__ == "__main__":
    print(solve_puzzle())