import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4']
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    mothers = ['Janelle', 'Holly', 'Aniya', 'Kailyn']
    smoothies = ['watermelon', 'dragonfruit', 'desert', 'cherry']
    heights = ['tall', 'average', 'short', 'very short']
    educations = ['high school', 'associate', 'master', 'bachelor']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for smoothie_perm in permutations(smoothies):
                for height_perm in permutations(heights):
                    for education_perm in permutations(educations):
                        # Create a dictionary to hold the current assignment
                        assignment = {
                            '1': {'Name': None, "mother's name": None, 'smoothie': None, 'height': None, 'education': None},
                            '2': {'Name': None, "mother's name": None, 'smoothie': None, 'height': None, 'education': None},
                            '3': {'Name': None, "mother's name": None, 'smoothie': None, 'height': None, 'education': None},
                            '4': {'Name': None, "mother's name": None, 'smoothie': None, 'height': None, 'education': None}
                        }
                        
                        # Assign current permutation values to houses
                        for i, house in enumerate(houses):
                            assignment[house]['Name'] = name_perm[i]
                            assignment[house]["mother's name"] = mother_perm[i]
                            assignment[house]['smoothie'] = smoothie_perm[i]
                            assignment[house]['height'] = height_perm[i]
                            assignment[house]['education'] = education_perm[i]
                        
                        # Check all constraints
                        # Constraint 1: Janelle is in house 3
                        if assignment['3']["mother's name"] != 'Janelle':
                            continue
                        
                        # Constraint 2: Desert smoothie lover has master's degree
                        desert_house = None
                        for house in houses:
                            if assignment[house]['smoothie'] == 'desert':
                                desert_house = house
                                break
                        if desert_house is None or assignment[desert_house]['education'] != 'master':
                            continue
                        
                        # Constraint 3: Desert smoothie lover is not in house 1
                        if desert_house == '1':
                            continue
                        
                        # Constraint 4: very short is left of high school
                        very_short_house = None
                        high_school_house = None
                        for house in houses:
                            if assignment[house]['height'] == 'very short':
                                very_short_house = house
                            if assignment[house]['education'] == 'high school':
                                high_school_house = house
                        if very_short_house is None or high_school_house is None or int(very_short_house) >= int(high_school_house):
                            continue
                        
                        # Constraint 5: Eric and cherry lover are next to each other
                        eric_house = None
                        cherry_house = None
                        for house in houses:
                            if assignment[house]['Name'] == 'Eric':
                                eric_house = house
                            if assignment[house]['smoothie'] == 'cherry':
                                cherry_house = house
                        if eric_house is None or cherry_house is None or abs(int(eric_house) - int(cherry_house)) != 1:
                            continue
                        
                        # Constraint 6: high school is not in house 3
                        if high_school_house == '3':
                            continue
                        
                        # Constraint 7: Kailyn's child has associate degree
                        kailyn_house = None
                        for house in houses:
                            if assignment[house]["mother's name"] == 'Kailyn':
                                kailyn_house = house
                                break
                        if kailyn_house is None or assignment[kailyn_house]['education'] != 'associate':
                            continue
                        
                        # Constraint 8: cherry lover's mother is Aniya
                        if cherry_house is not None and assignment[cherry_house]["mother's name"] != 'Aniya':
                            continue
                        
                        # Constraint 9: tall person's mother is Janelle (house 3)
                        if assignment['3']['height'] != 'tall':
                            continue
                        
                        # Constraint 10: Arnold is right of average height
                        average_house = None
                        arnold_house = None
                        for house in houses:
                            if assignment[house]['height'] == 'average':
                                average_house = house
                            if assignment[house]['Name'] == 'Arnold':
                                arnold_house = house
                        if average_house is None or arnold_house is None or int(arnold_house) <= int(average_house):
                            continue
                        
                        # Constraint 11: dragonfruit is directly left of short
                        dragonfruit_house = None
                        short_house = None
                        for house in houses:
                            if assignment[house]['smoothie'] == 'dragonfruit':
                                dragonfruit_house = house
                            if assignment[house]['height'] == 'short':
                                short_house = house
                        if dragonfruit_house is None or short_house is None or int(short_house) - int(dragonfruit_house) != 1:
                            continue
                        
                        # Constraint 12: tall person is Alice
                        if assignment['3']['Name'] != 'Alice':
                            continue
                        
                        # If all constraints are satisfied, return the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "mother's name", "smoothie", "height", "education"],
                                "rows": []
                            }
                        }
                        for house in houses:
                            row = [
                                house,
                                assignment[house]['Name'],
                                assignment[house]["mother's name"],
                                assignment[house]['smoothie'],
                                assignment[house]['height'],
                                assignment[house]['education']
                            ]
                            solution["solution"]["rows"].append(row)
                        return solution
    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))