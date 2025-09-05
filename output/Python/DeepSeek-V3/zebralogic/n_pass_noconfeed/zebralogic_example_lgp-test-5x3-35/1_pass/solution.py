import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
    heights = ['average', 'very short', 'short', 'very tall', 'tall']
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for height_perm in permutations(heights):
                # Create assignment dictionaries
                assignment = {}
                for i, house in enumerate(houses):
                    assignment[house] = {
                        'name': name_perm[i],
                        'mother': mother_perm[i],
                        'height': height_perm[i]
                    }
                
                # Check all constraints
                valid = True
                
                # Clue 1: Alice is The person whose mother's name is Aniya
                alice_house = None
                aniya_house = None
                for house, attrs in assignment.items():
                    if attrs['name'] == 'Alice':
                        alice_house = house
                    if attrs['mother'] == 'Aniya':
                        aniya_house = house
                if alice_house != aniya_house:
                    valid = False
                
                # Clue 2: The person who has an average height is somewhere to the left of The person whose mother's name is Penny
                avg_height_house = None
                penny_mother_house = None
                for house, attrs in assignment.items():
                    if attrs['height'] == 'average':
                        avg_height_house = house
                    if attrs['mother'] == 'Penny':
                        penny_mother_house = house
                if not (avg_height_house and penny_mother_house and avg_height_house < penny_mother_house):
                    valid = False
                
                # Clue 3: The person whose mother's name is Janelle is Bob
                janelle_house = None
                bob_house = None
                for house, attrs in assignment.items():
                    if attrs['mother'] == 'Janelle':
                        janelle_house = house
                    if attrs['name'] == 'Bob':
                        bob_house = house
                if janelle_house != bob_house:
                    valid = False
                
                # Clue 4: Peter is not in the second house
                if assignment[2]['name'] == 'Peter':
                    valid = False
                
                # Clue 5: The person who is short is directly left of Arnold
                short_house = None
                arnold_house = None
                for house, attrs in assignment.items():
                    if attrs['height'] == 'short':
                        short_house = house
                    if attrs['name'] == 'Arnold':
                        arnold_house = house
                if not (short_house and arnold_house and short_house == arnold_house - 1):
                    valid = False
                
                # Clue 6: The person who is very tall is Arnold
                very_tall_house = None
                for house, attrs in assignment.items():
                    if attrs['height'] == 'very tall':
                        very_tall_house = house
                if not (very_tall_house and assignment[very_tall_house]['name'] == 'Arnold'):
                    valid = False
                
                # Clue 7: Bob is directly left of the person who has an average height
                bob_house = None
                avg_height_house = None
                for house, attrs in assignment.items():
                    if attrs['name'] == 'Bob':
                        bob_house = house
                    if attrs['height'] == 'average':
                        avg_height_house = house
                if not (bob_house and avg_height_house and bob_house == avg_height_house - 1):
                    valid = False
                
                # Clue 8: Eric is not in the fifth house
                if assignment[5]['name'] == 'Eric':
                    valid = False
                
                # Clue 9: The person who is very tall is somewhere to the right of The person whose mother's name is Holly
                very_tall_house = None
                holly_mother_house = None
                for house, attrs in assignment.items():
                    if attrs['height'] == 'very tall':
                        very_tall_house = house
                    if attrs['mother'] == 'Holly':
                        holly_mother_house = house
                if not (very_tall_house and holly_mother_house and very_tall_house > holly_mother_house):
                    valid = False
                
                # Clue 10: Eric is The person whose mother's name is Kailyn
                eric_house = None
                kailyn_house = None
                for house, attrs in assignment.items():
                    if attrs['name'] == 'Eric':
                        eric_house = house
                    if attrs['mother'] == 'Kailyn':
                        kailyn_house = house
                if eric_house != kailyn_house:
                    valid = False
                
                # Clue 11: The person who is very short is in the fifth house
                if assignment[5]['height'] != 'very short':
                    valid = False
                
                if valid:
                    # Format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Height"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        attrs = assignment[house]
                        solution["solution"]["rows"].append([
                            str(house),
                            attrs['name'],
                            attrs['mother'],
                            attrs['height']
                        ])
                    
                    return solution
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()