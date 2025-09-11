import json
from itertools import permutations

def main():
    names = ['Alice', 'Peter', 'Eric', 'Arnold']
    heights = ['very short', 'tall', 'very tall']
    mothers = ['Janelle', 'Penny', 'Holly', 'Aniya']
    hair_colors = ['blonde', 'black', 'gray', 'red', 'brown']
    
    for n_perm in permutations(names):
        for h_perm in permutations(heights):
            for m_perm in permutations(mothers):
                for hair_perm in permutations(hair_colors):
                    assignment = [
                        {'Name': n_perm[0], 'Height': 'average', 'Mother': m_perm[0], 'HairColor': hair_perm[0]},
                        {'Name': n_perm[1], 'Height': h_perm[0], 'Mother': m_perm[1], 'HairColor': hair_perm[1]},
                        {'Name': n_perm[2], 'Height': h_perm[1], 'Mother': 'Kailyn', 'HairColor': hair_perm[2]},
                        {'Name': n_perm[3], 'Height': 'short', 'Mother': m_perm[2], 'HairColor': hair_perm[3]},
                        {'Name': 'Bob', 'Height': h_perm[2], 'Mother': m_perm[3], 'HairColor': hair_perm[4]}
                    ]
                    
                    if check_constraints(assignment):
                        output_solution(assignment)
                        return

def check_constraints(assignment):
    # Clue 1: Tall height is Holly mother
    tall_house = None
    for i, house in enumerate(assignment):
        if house['Height'] == 'tall':
            tall_house = i
    if tall_house is None or assignment[tall_house]['Mother'] != 'Holly':
        return False

    # Clue 3: Gray hair left of Janelle mother
    gray_house = None
    janelle_house = None
    for i, house in enumerate(assignment):
        if house['HairColor'] == 'gray':
            gray_house = i
        if house['Mother'] == 'Janelle':
            janelle_house = i
    if gray_house is None or janelle_house is None or gray_house + 1 != janelle_house:
        return False

    # Clue 4: Black hair not in house 4
    if assignment[3]['HairColor'] == 'black':
        return False

    # Clue 5: Eric has black hair
    eric_house = None
    for i, house in enumerate(assignment):
        if house['Name'] == 'Eric':
            eric_house = i
    if eric_house is None or assignment[eric_house]['HairColor'] != 'black':
        return False

    # Clue 6: Very short is Penny mother
    very_short_house = None
    for i, house in enumerate(assignment):
        if house['Height'] == 'very short':
            very_short_house = i
    if very_short_house is None or assignment[very_short_house]['Mother'] != 'Penny':
        return False

    # Clue 7: Eric and gray hair adjacent
    gray_house = None
    for i, house in enumerate(assignment):
        if house['HairColor'] == 'gray':
            gray_house = i
    if gray_house is None or abs(eric_house - gray_house) != 1:
        return False

    # Clue 9: Red hair is Peter
    peter_house = None
    for i, house in enumerate(assignment):
        if house['Name'] == 'Peter':
            peter_house = i
    if peter_house is None or assignment[peter_house]['HairColor'] != 'red':
        return False

    # Clue 11: Arnold has brown hair
    arnold_house = None
    for i, house in enumerate(assignment):
        if house['Name'] == 'Arnold':
            arnold_house = i
    if arnold_house is None or assignment[arnold_house]['HairColor'] != 'brown':
        return False

    # Clue 12: Brown hair left of Janelle mother
    brown_hair_house = None
    for i, house in enumerate(assignment):
        if house['HairColor'] == 'brown':
            brown_hair_house = i
    if brown_hair_house is None or brown_hair_house >= janelle_house:
        return False

    # Clue 13: Aniya mother and very short adjacent
    aniya_house = None
    for i, house in enumerate(assignment):
        if house['Mother'] == 'Aniya':
            aniya_house = i
    if aniya_house is None or abs(aniya_house - very_short_house) != 1:
        return False

    return True

def output_solution(assignment):
    result = {
        "solution": {
            "header": ["House", "Name", "Height", "Mother", "HairColor"],
            "rows": []
        }
    }
    for i, house in enumerate(assignment):
        result["solution"]["rows"].append([
            str(i+1),
            house['Name'],
            house['Height'],
            house['Mother'],
            house['HairColor']
        ])
    print(json.dumps(result))

if __name__ == "__main__":
    main()