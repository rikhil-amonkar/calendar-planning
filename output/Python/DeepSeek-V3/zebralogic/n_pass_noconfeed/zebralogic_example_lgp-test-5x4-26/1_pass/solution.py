import json
from itertools import permutations

def main():
    # Define all possible values
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    heights = ['very short', 'short', 'tall', 'average', 'very tall']
    mothers = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
    hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']
    
    houses = [1, 2, 3, 4, 5]
    
    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for height_perm in permutations(heights):
            for mother_perm in permutations(mothers):
                for hair_perm in permutations(hair_colors):
                    # Create assignment dictionaries for each house
                    assignment = {}
                    for i, house in enumerate(houses):
                        assignment[house] = {
                            'Name': name_perm[i],
                            'Height': height_perm[i],
                            'Mother': mother_perm[i],
                            'HairColor': hair_perm[i]
                        }
                    
                    # Check all constraints
                    # Clue 1: The person who is tall is The person whose mother's name is Holly.
                    tall_house = None
                    holly_house = None
                    for house in houses:
                        if assignment[house]['Height'] == 'tall':
                            tall_house = house
                        if assignment[house]['Mother'] == 'Holly':
                            holly_house = house
                    if tall_house != holly_house:
                        continue
                    
                    # Clue 2: There are two houses between the person who has an average height and the person who is short.
                    avg_house = None
                    short_house = None
                    for house in houses:
                        if assignment[house]['Height'] == 'average':
                            avg_house = house
                        if assignment[house]['Height'] == 'short':
                            short_house = house
                    if avg_house is None or short_house is None or abs(avg_house - short_house) != 3:
                        continue
                    
                    # Clue 3: The person who has gray hair is directly left of The person whose mother's name is Janelle.
                    gray_hair_house = None
                    janelle_house = None
                    for house in houses:
                        if assignment[house]['HairColor'] == 'gray':
                            gray_hair_house = house
                        if assignment[house]['Mother'] == 'Janelle':
                            janelle_house = house
                    if gray_hair_house is None or janelle_house is None or gray_hair_house + 1 != janelle_house:
                        continue
                    
                    # Clue 4: The person who has black hair is not in the fourth house.
                    black_hair_house = None
                    for house in houses:
                        if assignment[house]['HairColor'] == 'black':
                            black_hair_house = house
                    if black_hair_house == 4:
                        continue
                    
                    # Clue 5: Eric is the person who has black hair.
                    eric_house = None
                    for house in houses:
                        if assignment[house]['Name'] == 'Eric':
                            eric_house = house
                    if eric_house != black_hair_house:
                        continue
                    
                    # Clue 6: The person who is very short is The person whose mother's name is Penny.
                    very_short_house = None
                    penny_house = None
                    for house in houses:
                        if assignment[house]['Height'] == 'very short':
                            very_short_house = house
                        if assignment[house]['Mother'] == 'Penny':
                            penny_house = house
                    if very_short_house != penny_house:
                        continue
                    
                    # Clue 7: Eric and the person who has gray hair are next to each other.
                    if eric_house is None or gray_hair_house is None or abs(eric_house - gray_hair_house) != 1:
                        continue
                    
                    # Clue 8: Bob is in the fifth house.
                    if assignment[5]['Name'] != 'Bob':
                        continue
                    
                    # Clue 9: The person who has red hair is Peter.
                    red_hair_house = None
                    peter_house = None
                    for house in houses:
                        if assignment[house]['HairColor'] == 'red':
                            red_hair_house = house
                        if assignment[house]['Name'] == 'Peter':
                            peter_house = house
                    if red_hair_house != peter_house:
                        continue
                    
                    # Clue 10: The person whose mother's name is Kailyn is directly left of the person who is short.
                    kailyn_house = None
                    for house in houses:
                        if assignment[house]['Mother'] == 'Kailyn':
                            kailyn_house = house
                    if kailyn_house is None or short_house is None or kailyn_house + 1 != short_house:
                        continue
                    
                    # Clue 11: Arnold is the person who has brown hair.
                    arnold_house = None
                    brown_hair_house = None
                    for house in houses:
                        if assignment[house]['Name'] == 'Arnold':
                            arnold_house = house
                        if assignment[house]['HairColor'] == 'brown':
                            brown_hair_house = house
                    if arnold_house != brown_hair_house:
                        continue
                    
                    # Clue 12: The person who has brown hair is somewhere to the left of The person whose mother's name is Janelle.
                    if brown_hair_house >= janelle_house:
                        continue
                    
                    # Clue 13: The person whose mother's name is Aniya and the person who is very short are next to each other.
                    aniya_house = None
                    for house in houses:
                        if assignment[house]['Mother'] == 'Aniya':
                            aniya_house = house
                    if aniya_house is None or very_short_house is None or abs(aniya_house - very_short_house) != 1:
                        continue
                    
                    # Clue 14: The person whose mother's name is Kailyn is in the third house.
                    if kailyn_house != 3:
                        continue
                    
                    # If we reach here, all constraints are satisfied
                    # Format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Height", "Mother", "HairColor"],
                            "rows": []
                        }
                    }
                    
                    for house in sorted(assignment.keys()):
                        row = [
                            str(house),
                            assignment[house]['Name'],
                            assignment[house]['Height'],
                            assignment[house]['Mother'],
                            assignment[house]['HairColor']
                        ]
                        solution["solution"]["rows"].append(row)
                    
                    print(json.dumps(solution, indent=2))
                    return
    
    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()