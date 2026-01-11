import json
from itertools import permutations

def solve():
    # Define all possible values for each category
    names = ["Peter", "Arnold", "Eric", "Alice"]
    flowers = ["daffodils", "carnations", "roses", "lilies"]
    heights = ["very short", "short", "tall", "average"]
    mothers = ["Janelle", "Kailyn", "Holly", "Aniya"]
    occupations = ["engineer", "doctor", "teacher", "artist"]
    sports = ["swimming", "basketball", "tennis", "soccer"]
    
    houses = [1, 2, 3, 4]
    
    # Generate all permutations for each category across 4 houses
    for name_perm in permutations(names, 4):
        for flower_perm in permutations(flowers, 4):
            for height_perm in permutations(heights, 4):
                for mother_perm in permutations(mothers, 4):
                    for occ_perm in permutations(occupations, 4):
                        for sport_perm in permutations(sports, 4):
                            
                            # Create assignment dictionaries
                            assignment = {}
                            for i in range(4):
                                house = i + 1
                                assignment[house] = {
                                    'Name': name_perm[i],
                                    'Flower': flower_perm[i],
                                    'Height': height_perm[i],
                                    'Mother': mother_perm[i],
                                    'Occupation': occ_perm[i],
                                    'FavoriteSport': sport_perm[i]
                                }
                            
                            # Check all clues
                            valid = True
                            
                            # Clue 1: swimming person = rose person
                            swimming_house = None
                            rose_house = None
                            for house in houses:
                                if assignment[house]['FavoriteSport'] == 'swimming':
                                    swimming_house = house
                                if assignment[house]['Flower'] == 'roses':
                                    rose_house = house
                            if swimming_house != rose_house:
                                valid = False
                            
                            # Clue 2: rose person = Eric
                            eric_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Eric':
                                    eric_house = house
                            if rose_house != eric_house:
                                valid = False
                            
                            # Clue 3: Arnold is tall
                            arnold_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Arnold':
                                    arnold_house = house
                                    if assignment[house]['Height'] != 'tall':
                                        valid = False
                            if arnold_house is None:
                                valid = False
                            
                            # Clue 4: daffodils is somewhere to the right of engineer
                            engineer_house = None
                            daffodils_house = None
                            for house in houses:
                                if assignment[house]['Occupation'] == 'engineer':
                                    engineer_house = house
                                if assignment[house]['Flower'] == 'daffodils':
                                    daffodils_house = house
                            if not (engineer_house is not None and daffodils_house is not None and daffodils_house > engineer_house):
                                valid = False
                            
                            # Clue 5: soccer person = short person
                            soccer_house = None
                            short_house = None
                            for house in houses:
                                if assignment[house]['FavoriteSport'] == 'soccer':
                                    soccer_house = house
                                if assignment[house]['Height'] == 'short':
                                    short_house = house
                            if soccer_house != short_house:
                                valid = False
                            
                            # Clue 6: teacher is in first house
                            if assignment[1]['Occupation'] != 'teacher':
                                valid = False
                            
                            # Clue 7: Janelle mother = carnations
                            janelle_house = None
                            carnations_house = None
                            for house in houses:
                                if assignment[house]['Mother'] == 'Janelle':
                                    janelle_house = house
                                if assignment[house]['Flower'] == 'carnations':
                                    carnations_house = house
                            if janelle_house != carnations_house:
                                valid = False
                            
                            # Clue 8: basketball person = average height person
                            basketball_house = None
                            average_house = None
                            for house in houses:
                                if assignment[house]['FavoriteSport'] == 'basketball':
                                    basketball_house = house
                                if assignment[house]['Height'] == 'average':
                                    average_house = house
                            if basketball_house != average_house:
                                valid = False
                            
                            # Clue 9: Arnold is not in third house
                            if arnold_house == 3:
                                valid = False
                            
                            # Clue 10: Holly mother is somewhere to the right of average height person
                            holly_house = None
                            for house in houses:
                                if assignment[house]['Mother'] == 'Holly':
                                    holly_house = house
                            if not (holly_house is not None and average_house is not None and holly_house > average_house):
                                valid = False
                            
                            # Clue 11: Peter is doctor
                            peter_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Peter':
                                    peter_house = house
                                    if assignment[house]['Occupation'] != 'doctor':
                                        valid = False
                            if peter_house is None:
                                valid = False
                            
                            # Clue 12: Aniya mother is Alice
                            aniya_house = None
                            alice_house = None
                            for house in houses:
                                if assignment[house]['Mother'] == 'Aniya':
                                    aniya_house = house
                                if assignment[house]['Name'] == 'Alice':
                                    alice_house = house
                            if aniya_house != alice_house:
                                valid = False
                            
                            # Clue 13: Arnold loves lilies
                            if arnold_house is not None and assignment[arnold_house]['Flower'] != 'lilies':
                                valid = False
                            
                            if valid:
                                # Found solution
                                result = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                                        "rows": []
                                    }
                                }
                                
                                for house in houses:
                                    row = [
                                        str(house),
                                        assignment[house]['Name'],
                                        assignment[house]['Flower'],
                                        assignment[house]['Height'],
                                        assignment[house]['Mother'],
                                        assignment[house]['Occupation'],
                                        assignment[house]['FavoriteSport']
                                    ]
                                    result["solution"]["rows"].append(row)
                                
                                return result
    
    return None

def main():
    solution = solve()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()