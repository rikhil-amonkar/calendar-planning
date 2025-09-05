import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ["Peter", "Arnold", "Eric", "Alice"]
    flowers = ["daffodils", "carnations", "roses", "lilies"]
    heights = ["very short", "short", "tall", "average"]
    mothers = ["Janelle", "Kailyn", "Holly", "Aniya"]
    occupations = ["engineer", "doctor", "teacher", "artist"]
    sports = ["swimming", "basketball", "tennis", "soccer"]
    
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for flower_perm in permutations(flowers):
            for height_perm in permutations(heights):
                for mother_perm in permutations(mothers):
                    for occupation_perm in permutations(occupations):
                        for sport_perm in permutations(sports):
                            # Create assignment for each house
                            assignment = {}
                            for i, house in enumerate(houses):
                                assignment[house] = {
                                    "Name": name_perm[i],
                                    "Flower": flower_perm[i],
                                    "Height": height_perm[i],
                                    "Mother": mother_perm[i],
                                    "Occupation": occupation_perm[i],
                                    "FavoriteSport": sport_perm[i]
                                }
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: The person who loves swimming is the person who loves the rose bouquet.
                            swimming_sport = None
                            rose_flower = None
                            for house, attrs in assignment.items():
                                if attrs["FavoriteSport"] == "swimming":
                                    swimming_sport = house
                                if attrs["Flower"] == "roses":
                                    rose_flower = house
                            if swimming_sport != rose_flower:
                                valid = False
                            
                            # Clue 2: The person who loves the rose bouquet is Eric.
                            if valid:
                                for house, attrs in assignment.items():
                                    if attrs["Flower"] == "roses" and attrs["Name"] != "Eric":
                                        valid = False
                                        break
                            
                            # Clue 3: Arnold is the person who is tall.
                            if valid:
                                for house, attrs in assignment.items():
                                    if attrs["Name"] == "Arnold" and attrs["Height"] != "tall":
                                        valid = False
                                        break
                            
                            # Clue 4: The person who loves a bouquet of daffodils is somewhere to the right of the person who is an engineer.
                            if valid:
                                daffodil_house = None
                                engineer_house = None
                                for house, attrs in assignment.items():
                                    if attrs["Flower"] == "daffodils":
                                        daffodil_house = house
                                    if attrs["Occupation"] == "engineer":
                                        engineer_house = house
                                if not (daffodil_house and engineer_house and daffodil_house > engineer_house):
                                    valid = False
                            
                            # Clue 5: The person who loves soccer is the person who is short.
                            if valid:
                                for house, attrs in assignment.items():
                                    if attrs["FavoriteSport"] == "soccer" and attrs["Height"] != "short":
                                        valid = False
                                        break
                            
                            # Clue 6: The person who is a teacher is in the first house.
                            if valid:
                                if assignment[1]["Occupation"] != "teacher":
                                    valid = False
                            
                            # Clue 7: The person whose mother's name is Janelle is the person who loves a carnations arrangement.
                            if valid:
                                for house, attrs in assignment.items():
                                    if attrs["Mother"] == "Janelle" and attrs["Flower"] != "carnations":
                                        valid = False
                                        break
                            
                            # Clue 8: The person who loves basketball is the person who has an average height.
                            if valid:
                                for house, attrs in assignment.items():
                                    if attrs["FavoriteSport"] == "basketball" and attrs["Height"] != "average":
                                        valid = False
                                        break
                            
                            # Clue 9: Arnold is not in the third house.
                            if valid:
                                if assignment[3]["Name"] == "Arnold":
                                    valid = False
                            
                            # Clue 10: The person whose mother's name is Holly is somewhere to the right of the person who has an average height.
                            if valid:
                                holly_house = None
                                avg_height_house = None
                                for house, attrs in assignment.items():
                                    if attrs["Mother"] == "Holly":
                                        holly_house = house
                                    if attrs["Height"] == "average":
                                        avg_height_house = house
                                if not (holly_house and avg_height_house and holly_house > avg_height_house):
                                    valid = False
                            
                            # Clue 11: Peter is the person who is a doctor.
                            if valid:
                                for house, attrs in assignment.items():
                                    if attrs["Name"] == "Peter" and attrs["Occupation"] != "doctor":
                                        valid = False
                                        break
                            
                            # Clue 12: The person whose mother's name is Aniya is Alice.
                            if valid:
                                for house, attrs in assignment.items():
                                    if attrs["Mother"] == "Aniya" and attrs["Name"] != "Alice":
                                        valid = False
                                        break
                            
                            # Clue 13: Arnold is the person who loves the bouquet of lilies.
                            if valid:
                                for house, attrs in assignment.items():
                                    if attrs["Name"] == "Arnold" and attrs["Flower"] != "lilies":
                                        valid = False
                                        break
                            
                            if valid:
                                # Format the solution
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
                                        "rows": []
                                    }
                                }
                                
                                for house in sorted(assignment.keys()):
                                    attrs = assignment[house]
                                    row = [
                                        str(house),
                                        attrs["Name"],
                                        attrs["Flower"],
                                        attrs["Height"],
                                        attrs["Mother"],
                                        attrs["Occupation"],
                                        attrs["FavoriteSport"]
                                    ]
                                    solution["solution"]["rows"].append(row)
                                
                                print(json.dumps(solution, indent=2))
                                return

if __name__ == "__main__":
    main()