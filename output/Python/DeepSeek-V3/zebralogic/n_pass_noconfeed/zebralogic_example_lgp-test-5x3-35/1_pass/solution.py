import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob']
    mothers = ['Kailyn', 'Janelle', 'Aniya', 'Penny', 'Holly']
    heights = ['average', 'very short', 'short', 'very tall', 'tall']
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for height_perm in permutations(heights):
                # Create assignment for each house (1-5)
                assignment = {}
                for i in range(5):
                    house = i + 1
                    assignment[house] = {
                        'Name': name_perm[i],
                        'Mother': mother_perm[i],
                        'Height': height_perm[i]
                    }
                
                # Check all constraints
                # Clue 1: Alice is The person whose mother's name is Aniya.
                clue1_ok = False
                for house in range(1, 6):
                    if (assignment[house]['Name'] == 'Alice' and 
                        assignment[house]['Mother'] == 'Aniya'):
                        clue1_ok = True
                        break
                if not clue1_ok:
                    continue
                
                # Clue 2: The person who has an average height is somewhere to the left of 
                # The person whose mother's name is Penny.
                clue2_ok = False
                avg_height_house = None
                penny_mother_house = None
                for house in range(1, 6):
                    if assignment[house]['Height'] == 'average':
                        avg_height_house = house
                    if assignment[house]['Mother'] == 'Penny':
                        penny_mother_house = house
                if (avg_height_house is not None and penny_mother_house is not None and
                    avg_height_house < penny_mother_house):
                    clue2_ok = True
                if not clue2_ok:
                    continue
                
                # Clue 3: The person whose mother's name is Janelle is Bob.
                clue3_ok = False
                for house in range(1, 6):
                    if (assignment[house]['Mother'] == 'Janelle' and 
                        assignment[house]['Name'] == 'Bob'):
                        clue3_ok = True
                        break
                if not clue3_ok:
                    continue
                
                # Clue 4: Peter is not in the second house.
                clue4_ok = assignment[2]['Name'] != 'Peter'
                if not clue4_ok:
                    continue
                
                # Clue 5: The person who is short is directly left of Arnold.
                clue5_ok = False
                for house in range(1, 5):  # Check houses 1-4
                    if (assignment[house]['Height'] == 'short' and 
                        assignment[house + 1]['Name'] == 'Arnold'):
                        clue5_ok = True
                        break
                if not clue5_ok:
                    continue
                
                # Clue 6: The person who is very tall is Arnold.
                clue6_ok = False
                for house in range(1, 6):
                    if (assignment[house]['Height'] == 'very tall' and 
                        assignment[house]['Name'] == 'Arnold'):
                        clue6_ok = True
                        break
                if not clue6_ok:
                    continue
                
                # Clue 7: Bob is directly left of the person who has an average height.
                clue7_ok = False
                for house in range(1, 5):  # Check houses 1-4
                    if (assignment[house]['Name'] == 'Bob' and 
                        assignment[house + 1]['Height'] == 'average'):
                        clue7_ok = True
                        break
                if not clue7_ok:
                    continue
                
                # Clue 8: Eric is not in the fifth house.
                clue8_ok = assignment[5]['Name'] != 'Eric'
                if not clue8_ok:
                    continue
                
                # Clue 9: The person who is very tall is somewhere to the right of 
                # The person whose mother's name is Holly.
                clue9_ok = False
                very_tall_house = None
                holly_mother_house = None
                for house in range(1, 6):
                    if assignment[house]['Height'] == 'very tall':
                        very_tall_house = house
                    if assignment[house]['Mother'] == 'Holly':
                        holly_mother_house = house
                if (very_tall_house is not None and holly_mother_house is not None and
                    very_tall_house > holly_mother_house):
                    clue9_ok = True
                if not clue9_ok:
                    continue
                
                # Clue 10: Eric is The person whose mother's name is Kailyn.
                clue10_ok = False
                for house in range(1, 6):
                    if (assignment[house]['Name'] == 'Eric' and 
                        assignment[house]['Mother'] == 'Kailyn'):
                        clue10_ok = True
                        break
                if not clue10_ok:
                    continue
                
                # Clue 11: The person who is very short is in the fifth house.
                clue11_ok = assignment[5]['Height'] == 'very short'
                if not clue11_ok:
                    continue
                
                # If we reach here, all constraints are satisfied
                # Format the solution as required
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Height"],
                        "rows": []
                    }
                }
                
                for house in range(1, 6):
                    row = [
                        str(house),
                        assignment[house]['Name'],
                        assignment[house]['Mother'],
                        assignment[house]['Height']
                    ]
                    solution["solution"]["rows"].append(row)
                
                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return
    
    # If no solution found (shouldn't happen with valid puzzle)
    print(json.dumps({"solution": {"header": ["House", "Name", "Mother", "Height"], "rows": []}}))

if __name__ == "__main__":
    main()