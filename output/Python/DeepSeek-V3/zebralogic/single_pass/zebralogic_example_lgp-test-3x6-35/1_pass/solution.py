import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3']
    names = ['Eric', 'Arnold', 'Peter']
    vacations = ['mountain', 'city', 'beach']
    heights = ['very short', 'average', 'short']
    flowers = ['carnations', 'daffodils', 'lilies']
    hair_colors = ['brown', 'black', 'blonde']
    educations = ['associate', 'bachelor', 'high school']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for vac_perm in permutations(vacations):
            for height_perm in permutations(heights):
                for flower_perm in permutations(flowers):
                    for hair_perm in permutations(hair_colors):
                        for edu_perm in permutations(educations):
                            # Create a solution dictionary
                            solution = {
                                '1': {
                                    'Name': name_perm[0],
                                    'Vacation': vac_perm[0],
                                    'Height': height_perm[0],
                                    'Flower': flower_perm[0],
                                    'HairColor': hair_perm[0],
                                    'Education': edu_perm[0]
                                },
                                '2': {
                                    'Name': name_perm[1],
                                    'Vacation': vac_perm[1],
                                    'Height': height_perm[1],
                                    'Flower': flower_perm[1],
                                    'HairColor': hair_perm[1],
                                    'Education': edu_perm[1]
                                },
                                '3': {
                                    'Name': name_perm[2],
                                    'Vacation': vac_perm[2],
                                    'Height': height_perm[2],
                                    'Flower': flower_perm[2],
                                    'HairColor': hair_perm[2],
                                    'Education': edu_perm[2]
                                }
                            }

                            # Check all constraints
                            # 1. Peter is the person who has an average height.
                            peter_house = None
                            for house in houses:
                                if solution[house]['Name'] == 'Peter':
                                    peter_house = house
                                    break
                            if peter_house is None or solution[peter_house]['Height'] != 'average':
                                continue

                            # 2. The person who loves a bouquet of daffodils is Arnold.
                            arnold_house = None
                            for house in houses:
                                if solution[house]['Name'] == 'Arnold':
                                    arnold_house = house
                                    break
                            if arnold_house is None or solution[arnold_house]['Flower'] != 'daffodils':
                                continue

                            # 3. The person who is very short is not in the second house.
                            very_short_house = None
                            for house in houses:
                                if solution[house]['Height'] == 'very short':
                                    very_short_house = house
                                    break
                            if very_short_house == '2':
                                continue

                            # 4. The person who loves beach vacations is in the first house.
                            if solution['1']['Vacation'] != 'beach':
                                continue

                            # 5. The person with a high school diploma is in the third house.
                            if solution['3']['Education'] != 'high school':
                                continue

                            # 6. The person who is short is somewhere to the right of the person who is very short.
                            short_house = None
                            for house in houses:
                                if solution[house]['Height'] == 'short':
                                    short_house = house
                                    break
                            if very_short_house is None or short_house is None or int(short_house) <= int(very_short_house):
                                continue

                            # 7. The person who loves the bouquet of lilies is Eric.
                            eric_house = None
                            for house in houses:
                                if solution[house]['Name'] == 'Eric':
                                    eric_house = house
                                    break
                            if eric_house is None or solution[eric_house]['Flower'] != 'lilies':
                                continue

                            # 8. The person who loves the bouquet of lilies is the person with a bachelor's degree.
                            if solution[eric_house]['Education'] != 'bachelor':
                                continue

                            # 9. The person who prefers city breaks is somewhere to the right of Peter.
                            city_house = None
                            for house in houses:
                                if solution[house]['Vacation'] == 'city':
                                    city_house = house
                                    break
                            if city_house is None or int(city_house) <= int(peter_house):
                                continue

                            # 10. The person who has blonde hair is in the third house.
                            if solution['3']['HairColor'] != 'blonde':
                                continue

                            # 11. The person who loves beach vacations is the person who has brown hair.
                            if solution['1']['HairColor'] != 'brown':
                                continue

                            # If all constraints are satisfied, return the solution
                            result = {
                                "solution": {
                                    "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
                                    "rows": [
                                        ["1", solution['1']['Name'], solution['1']['Vacation'], solution['1']['Height'], solution['1']['Flower'], solution['1']['HairColor'], solution['1']['Education']],
                                        ["2", solution['2']['Name'], solution['2']['Vacation'], solution['2']['Height'], solution['2']['Flower'], solution['2']['HairColor'], solution['2']['Education']],
                                        ["3", solution['3']['Name'], solution['3']['Vacation'], solution['3']['Height'], solution['3']['Flower'], solution['3']['HairColor'], solution['3']['Education']]
                                    ]
                                }
                            }
                            return json.dumps(result, indent=2)

    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())