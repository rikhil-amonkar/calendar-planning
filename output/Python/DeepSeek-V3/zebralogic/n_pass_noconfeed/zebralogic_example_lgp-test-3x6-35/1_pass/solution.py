import json
from itertools import permutations

def main():
    # Define all possible values for each attribute
    names = ["Eric", "Arnold", "Peter"]
    vacations = ["mountain", "city", "beach"]
    heights = ["very short", "short", "average"]
    flowers = ["carnations", "daffodils", "lilies"]
    hair_colors = ["brown", "black", "blonde"]
    educations = ["associate", "bachelor", "high school"]
    
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for vac_perm in permutations(vacations):
            for height_perm in permutations(heights):
                for flower_perm in permutations(flowers):
                    for hair_perm in permutations(hair_colors):
                        for edu_perm in permutations(educations):
                            # Assign attributes to houses
                            assignment = []
                            for i in range(3):
                                house = {
                                    "House": str(i+1),
                                    "Name": name_perm[i],
                                    "Vacation": vac_perm[i],
                                    "Height": height_perm[i],
                                    "Flower": flower_perm[i],
                                    "HairColor": hair_perm[i],
                                    "Education": edu_perm[i]
                                }
                                assignment.append(house)
                            
                            # Check all constraints
                            valid = True
                            
                            # Clue 1: Peter is the person who has an average height.
                            peter_house = None
                            for house in assignment:
                                if house["Name"] == "Peter":
                                    peter_house = house
                                    break
                            if peter_house is None or peter_house["Height"] != "average":
                                valid = False
                                continue
                            
                            # Clue 2: The person who loves a bouquet of daffodils is Arnold.
                            for house in assignment:
                                if house["Flower"] == "daffodils" and house["Name"] != "Arnold":
                                    valid = False
                                    break
                                if house["Name"] == "Arnold" and house["Flower"] != "daffodils":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 3: The person who is very short is not in the second house.
                            for house in assignment:
                                if house["Height"] == "very short" and house["House"] == "2":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 4: The person who loves beach vacations is in the first house.
                            house1 = assignment[0]
                            if house1["Vacation"] != "beach":
                                valid = False
                                continue
                            
                            # Clue 5: The person with a high school diploma is in the third house.
                            house3 = assignment[2]
                            if house3["Education"] != "high school":
                                valid = False
                                continue
                            
                            # Clue 6: The person who is short is somewhere to the right of the person who is very short.
                            very_short_pos = None
                            short_pos = None
                            for i, house in enumerate(assignment):
                                if house["Height"] == "very short":
                                    very_short_pos = i
                                if house["Height"] == "short":
                                    short_pos = i
                            if very_short_pos is None or short_pos is None or short_pos <= very_short_pos:
                                valid = False
                                continue
                            
                            # Clue 7: The person who loves the bouquet of lilies is Eric.
                            for house in assignment:
                                if house["Flower"] == "lilies" and house["Name"] != "Eric":
                                    valid = False
                                    break
                                if house["Name"] == "Eric" and house["Flower"] != "lilies":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 8: The person who loves the bouquet of lilies is the person with a bachelor's degree.
                            for house in assignment:
                                if house["Flower"] == "lilies" and house["Education"] != "bachelor":
                                    valid = False
                                    break
                                if house["Education"] == "bachelor" and house["Flower"] != "lilies":
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # Clue 9: The person who prefers city breaks is somewhere to the right of Peter.
                            city_pos = None
                            for i, house in enumerate(assignment):
                                if house["Vacation"] == "city":
                                    city_pos = i
                            peter_pos = None
                            for i, house in enumerate(assignment):
                                if house["Name"] == "Peter":
                                    peter_pos = i
                                    break
                            if city_pos is None or peter_pos is None or city_pos <= peter_pos:
                                valid = False
                                continue
                            
                            # Clue 10: The person who has blonde hair is in the third house.
                            if house3["HairColor"] != "blonde":
                                valid = False
                                continue
                            
                            # Clue 11: The person who loves beach vacations is the person who has brown hair.
                            if house1["HairColor"] != "brown":
                                valid = False
                                continue
                            
                            # If we reach here, all constraints are satisfied
                            if valid:
                                # Format the solution as required
                                solution = {
                                    "solution": {
                                        "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                                        "rows": []
                                    }
                                }
                                
                                for house in assignment:
                                    row = [
                                        house["House"],
                                        house["Name"],
                                        house["Vacation"],
                                        house["Height"],
                                        house["Flower"],
                                        house["HairColor"],
                                        house["Education"]
                                    ]
                                    solution["solution"]["rows"].append(row)
                                
                                print(json.dumps(solution, indent=2))
                                return
    
    print('{"solution": {"header": [], "rows": []}}')

if __name__ == "__main__":
    main()