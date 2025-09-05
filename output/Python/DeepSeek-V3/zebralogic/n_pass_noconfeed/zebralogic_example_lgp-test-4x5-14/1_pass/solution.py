import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    mothers = ['Janelle', 'Holly', 'Aniya', 'Kailyn']
    smoothies = ['watermelon', 'dragonfruit', 'desert', 'cherry']
    heights = ['tall', 'average', 'short', 'very short']
    educations = ['high school', 'associate', 'master', 'bachelor']
    
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for mother_perm in permutations(mothers):
            for smoothie_perm in permutations(smoothies):
                for height_perm in permutations(heights):
                    for education_perm in permutations(educations):
                        # Create assignment dictionaries for each house
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                'name': name_perm[i],
                                'mother': mother_perm[i],
                                'smoothie': smoothie_perm[i],
                                'height': height_perm[i],
                                'education': education_perm[i]
                            }
                        
                        # Check all constraints
                        valid = True
                        
                        # Clue 1: The person whose mother's name is Janelle is in the third house.
                        if assignment[3]['mother'] != 'Janelle':
                            valid = False
                            continue
                        
                        # Clue 2: The Desert smoothie lover is the person with a master's degree.
                        desert_house = None
                        for house in houses:
                            if assignment[house]['smoothie'] == 'desert':
                                desert_house = house
                                break
                        if desert_house is None or assignment[desert_house]['education'] != 'master':
                            valid = False
                            continue
                        
                        # Clue 3: The Desert smoothie lover is not in the first house.
                        if desert_house == 1:
                            valid = False
                            continue
                        
                        # Clue 4: The person who is very short is somewhere to the left of the person with a high school diploma.
                        very_short_house = None
                        high_school_house = None
                        for house in houses:
                            if assignment[house]['height'] == 'very short':
                                very_short_house = house
                            if assignment[house]['education'] == 'high school':
                                high_school_house = house
                        if very_short_house is None or high_school_house is None or very_short_house >= high_school_house:
                            valid = False
                            continue
                        
                        # Clue 5: Eric and the person who likes Cherry smoothies are next to each other.
                        eric_house = None
                        cherry_house = None
                        for house in houses:
                            if assignment[house]['name'] == 'Eric':
                                eric_house = house
                            if assignment[house]['smoothie'] == 'cherry':
                                cherry_house = house
                        if eric_house is None or cherry_house is None or abs(eric_house - cherry_house) != 1:
                            valid = False
                            continue
                        
                        # Clue 6: The person with a high school diploma is not in the third house.
                        if assignment[3]['education'] == 'high school':
                            valid = False
                            continue
                        
                        # Clue 7: The person whose mother's name is Kailyn is the person with an associate's degree.
                        kailyn_house = None
                        for house in houses:
                            if assignment[house]['mother'] == 'Kailyn':
                                kailyn_house = house
                                break
                        if kailyn_house is None or assignment[kailyn_house]['education'] != 'associate':
                            valid = False
                            continue
                        
                        # Clue 8: The person who likes Cherry smoothies is The person whose mother's name is Aniya.
                        if cherry_house is None or assignment[cherry_house]['mother'] != 'Aniya':
                            valid = False
                            continue
                        
                        # Clue 9: The person who is tall is The person whose mother's name is Janelle.
                        tall_house = None
                        for house in houses:
                            if assignment[house]['height'] == 'tall':
                                tall_house = house
                                break
                        if tall_house is None or assignment[tall_house]['mother'] != 'Janelle':
                            valid = False
                            continue
                        
                        # Clue 10: Arnold is somewhere to the right of the person who has an average height.
                        arnold_house = None
                        average_height_house = None
                        for house in houses:
                            if assignment[house]['name'] == 'Arnold':
                                arnold_house = house
                            if assignment[house]['height'] == 'average':
                                average_height_house = house
                        if arnold_house is None or average_height_house is None or arnold_house <= average_height_house:
                            valid = False
                            continue
                        
                        # Clue 11: The Dragonfruit smoothie lover is directly left of the person who is short.
                        dragonfruit_house = None
                        short_house = None
                        for house in houses:
                            if assignment[house]['smoothie'] == 'dragonfruit':
                                dragonfruit_house = house
                            if assignment[house]['height'] == 'short':
                                short_house = house
                        if dragonfruit_house is None or short_house is None or dragonfruit_house + 1 != short_house:
                            valid = False
                            continue
                        
                        # Clue 12: The person who is tall is Alice.
                        if tall_house is None or assignment[tall_house]['name'] != 'Alice':
                            valid = False
                            continue
                        
                        # If all constraints are satisfied, we found the solution
                        if valid:
                            # Format the solution as required
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                                    "rows": []
                                }
                            }
                            
                            for house in sorted(assignment.keys()):
                                row = [
                                    str(house),
                                    assignment[house]['name'],
                                    assignment[house]['mother'],
                                    assignment[house]['smoothie'],
                                    assignment[house]['height'],
                                    assignment[house]['education']
                                ]
                                solution["solution"]["rows"].append(row)
                            
                            print(json.dumps(solution, indent=2))
                            return
    
    print('{"solution": {"header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"], "rows": []}}')

if __name__ == "__main__":
    main()