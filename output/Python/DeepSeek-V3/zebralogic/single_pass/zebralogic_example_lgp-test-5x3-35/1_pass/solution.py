import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
    heights = ['average', 'very short', 'short', 'very tall', 'tall']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for height_perm in permutations(heights):
                solution = []
                valid = True
                
                # Create a solution candidate
                for i in range(5):
                    house = str(i + 1)
                    name = name_perm[i]
                    mother = mother_perm[i]
                    height = height_perm[i]
                    solution.append([house, name, mother, height])
                
                # Check all constraints
                # Constraint 1: Alice's mother is Aniya
                alice_house = None
                aniya_house = None
                for house in solution:
                    if house[1] == 'Alice':
                        alice_house = house
                    if house[2] == 'Aniya':
                        aniya_house = house
                if alice_house is None or aniya_house is None or alice_house[2] != 'Aniya':
                    valid = False
                    continue
                
                # Constraint 2: average height is left of Penny's mother
                avg_house = None
                penny_house = None
                for house in solution:
                    if house[3] == 'average':
                        avg_house = house
                    if house[2] == 'Penny':
                        penny_house = house
                if avg_house is None or penny_house is None or int(avg_house[0]) >= int(penny_house[0]):
                    valid = False
                    continue
                
                # Constraint 3: Janelle's mother is Bob
                janelle_house = None
                bob_house = None
                for house in solution:
                    if house[2] == 'Janelle':
                        janelle_house = house
                    if house[1] == 'Bob':
                        bob_house = house
                if janelle_house is None or bob_house is None or janelle_house[1] != 'Bob':
                    valid = False
                    continue
                
                # Constraint 4: Peter is not in the second house
                if solution[1][1] == 'Peter':
                    valid = False
                    continue
                
                # Constraint 5: short is directly left of Arnold
                short_house = None
                arnold_house = None
                for house in solution:
                    if house[3] == 'short':
                        short_house = house
                    if house[1] == 'Arnold':
                        arnold_house = house
                if short_house is None or arnold_house is None or int(short_house[0]) + 1 != int(arnold_house[0]):
                    valid = False
                    continue
                
                # Constraint 6: very tall is Arnold
                for house in solution:
                    if house[1] == 'Arnold' and house[3] != 'very tall':
                        valid = False
                        break
                if not valid:
                    continue
                
                # Constraint 7: Bob is directly left of average height
                bob_house = None
                avg_house = None
                for house in solution:
                    if house[1] == 'Bob':
                        bob_house = house
                    if house[3] == 'average':
                        avg_house = house
                if bob_house is None or avg_house is None or int(bob_house[0]) + 1 != int(avg_house[0]):
                    valid = False
                    continue
                
                # Constraint 8: Eric is not in the fifth house
                if solution[4][1] == 'Eric':
                    valid = False
                    continue
                
                # Constraint 9: very tall is right of Holly's mother
                very_tall_house = None
                holly_house = None
                for house in solution:
                    if house[3] == 'very tall':
                        very_tall_house = house
                    if house[2] == 'Holly':
                        holly_house = house
                if very_tall_house is None or holly_house is None or int(very_tall_house[0]) <= int(holly_house[0]):
                    valid = False
                    continue
                
                # Constraint 10: Eric's mother is Kailyn
                eric_house = None
                kailyn_house = None
                for house in solution:
                    if house[1] == 'Eric':
                        eric_house = house
                    if house[2] == 'Kailyn':
                        kailyn_house = house
                if eric_house is None or kailyn_house is None or eric_house[2] != 'Kailyn':
                    valid = False
                    continue
                
                # Constraint 11: very short is in fifth house
                if solution[4][3] != 'very short':
                    valid = False
                    continue
                
                if valid:
                    return {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Height"],
                            "rows": solution
                        }
                    }
    
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))