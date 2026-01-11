import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each attribute
    names = ["Eric", "Arnold", "Peter"]
    vacations = ["mountain", "city", "beach"]
    heights = ["very short", "average", "short"]
    flowers = ["carnations", "daffodils", "lilies"]
    hair_colors = ["brown", "black", "blonde"]
    educations = ["associate", "bachelor", "high school"]
    
    houses = [1, 2, 3]
    
    # Generate all possible permutations for each attribute across 3 houses
    for name_perm in permutations(names):
        for vac_perm in permutations(vacations):
            for height_perm in permutations(heights):
                for flower_perm in permutations(flowers):
                    for hair_perm in permutations(hair_colors):
                        for edu_perm in permutations(educations):
                            
                            # Create assignment dictionaries
                            assignment = {}
                            for i in range(3):
                                assignment[i] = {
                                    'house': i+1,
                                    'name': name_perm[i],
                                    'vacation': vac_perm[i],
                                    'height': height_perm[i],
                                    'flower': flower_perm[i],
                                    'hair': hair_perm[i],
                                    'education': edu_perm[i]
                                }
                            
                            # Check all clues
                            valid = True
                            
                            # 1. Peter is the person who has an average height.
                            for i in range(3):
                                if assignment[i]['name'] == 'Peter' and assignment[i]['height'] != 'average':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # 2. The person who loves a bouquet of daffodils is Arnold.
                            for i in range(3):
                                if assignment[i]['flower'] == 'daffodils' and assignment[i]['name'] != 'Arnold':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # 3. The person who is very short is not in the second house.
                            for i in range(3):
                                if assignment[i]['height'] == 'very short' and assignment[i]['house'] == 2:
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # 4. The person who loves beach vacations is in the first house.
                            for i in range(3):
                                if assignment[i]['vacation'] == 'beach' and assignment[i]['house'] != 1:
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # 5. The person with a high school diploma is in the third house.
                            for i in range(3):
                                if assignment[i]['education'] == 'high school' and assignment[i]['house'] != 3:
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # 6. The person who is short is somewhere to the right of the person who is very short.
                            very_short_house = None
                            short_house = None
                            for i in range(3):
                                if assignment[i]['height'] == 'very short':
                                    very_short_house = assignment[i]['house']
                                if assignment[i]['height'] == 'short':
                                    short_house = assignment[i]['house']
                            if very_short_house is None or short_house is None or short_house <= very_short_house:
                                valid = False
                            if not valid:
                                continue
                            
                            # 7. The person who loves the bouquet of lilies is Eric.
                            for i in range(3):
                                if assignment[i]['flower'] == 'lilies' and assignment[i]['name'] != 'Eric':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # 8. The person who loves the bouquet of lilies is the person with a bachelor's degree.
                            for i in range(3):
                                if assignment[i]['flower'] == 'lilies' and assignment[i]['education'] != 'bachelor':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # 9. The person who prefers city breaks is somewhere to the right of Peter.
                            peter_house = None
                            city_house = None
                            for i in range(3):
                                if assignment[i]['name'] == 'Peter':
                                    peter_house = assignment[i]['house']
                                if assignment[i]['vacation'] == 'city':
                                    city_house = assignment[i]['house']
                            if peter_house is None or city_house is None or city_house <= peter_house:
                                valid = False
                            if not valid:
                                continue
                            
                            # 10. The person who has blonde hair is in the third house.
                            for i in range(3):
                                if assignment[i]['hair'] == 'blonde' and assignment[i]['house'] != 3:
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # 11. The person who loves beach vacations is the person who has brown hair.
                            for i in range(3):
                                if assignment[i]['vacation'] == 'beach' and assignment[i]['hair'] != 'brown':
                                    valid = False
                                    break
                            if not valid:
                                continue
                            
                            # If we get here, all clues are satisfied
                            # Prepare the solution in the required format
                            rows = []
                            for i in range(3):
                                row = [
                                    str(assignment[i]['house']),
                                    assignment[i]['name'],
                                    assignment[i]['vacation'],
                                    assignment[i]['height'],
                                    assignment[i]['flower'],
                                    assignment[i]['hair'],
                                    assignment[i]['education']
                                ]
                                rows.append(row)
                            
                            # Sort rows by house number
                            rows.sort(key=lambda x: int(x[0]))
                            
                            return {
                                "solution": {
                                    "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                                    "rows": rows
                                }
                            }
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()