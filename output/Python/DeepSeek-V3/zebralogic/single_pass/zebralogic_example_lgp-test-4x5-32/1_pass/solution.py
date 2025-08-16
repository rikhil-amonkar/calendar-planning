import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4']
    names = ['Arnold', 'Alice', 'Eric', 'Peter']
    hobbies = ['cooking', 'painting', 'photography', 'gardening']
    birthdays = ['april', 'jan', 'sept', 'feb']
    educations = ['master', 'bachelor', 'associate', 'high school']
    smoothies = ['cherry', 'watermelon', 'desert', 'dragonfruit']

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for hobby_perm in permutations(hobbies):
            for birthday_perm in permutations(birthdays):
                for education_perm in permutations(educations):
                    for smoothie_perm in permutations(smoothies):
                        # Create a dictionary to hold the current assignment
                        assignment = {}
                        for i in range(4):
                            house = houses[i]
                            assignment[house] = {
                                'Name': name_perm[i],
                                'Hobby': hobby_perm[i],
                                'Birthday': birthday_perm[i],
                                'Education': education_perm[i],
                                'Smoothie': smoothie_perm[i]
                            }

                        # Check all constraints
                        valid = True

                        # Clue 1: The Desert smoothie lover is the person whose birthday is in January.
                        for house in houses:
                            if assignment[house]['Smoothie'] == 'desert':
                                if assignment[house]['Birthday'] != 'jan':
                                    valid = False
                                break

                        # Clue 2: Eric is the person with a bachelor's degree.
                        for house in houses:
                            if assignment[house]['Name'] == 'Eric':
                                if assignment[house]['Education'] != 'bachelor':
                                    valid = False
                                break

                        # Clue 3: The person whose birthday is in January is the person with a bachelor's degree.
                        for house in houses:
                            if assignment[house]['Birthday'] == 'jan':
                                if assignment[house]['Education'] != 'bachelor':
                                    valid = False
                                break

                        # Clue 4: The person with a high school diploma is in the third house.
                        if assignment['3']['Education'] != 'high school':
                            valid = False

                        # Clue 5: The Watermelon smoothie lover is not in the third house.
                        if assignment['3']['Smoothie'] == 'watermelon':
                            valid = False

                        # Clue 6: The person with an associate's degree is Arnold.
                        for house in houses:
                            if assignment[house]['Name'] == 'Arnold':
                                if assignment[house]['Education'] != 'associate':
                                    valid = False
                                break

                        # Clue 7: The person with a master's degree is the person who paints as a hobby.
                        for house in houses:
                            if assignment[house]['Education'] == 'master':
                                if assignment[house]['Hobby'] != 'painting':
                                    valid = False
                                break

                        # Clue 8: There is one house between the Dragonfruit smoothie lover and the person whose birthday is in September.
                        dragonfruit_house = None
                        sept_house = None
                        for house in houses:
                            if assignment[house]['Smoothie'] == 'dragonfruit':
                                dragonfruit_house = int(house)
                            if assignment[house]['Birthday'] == 'sept':
                                sept_house = int(house)
                        if dragonfruit_house is not None and sept_house is not None:
                            if abs(dragonfruit_house - sept_house) != 2:
                                valid = False
                        else:
                            valid = False

                        # Clue 9: The person with a high school diploma is the person whose birthday is in September.
                        if assignment['3']['Birthday'] != 'sept':
                            valid = False

                        # Clue 10: The person who loves cooking is Alice.
                        for house in houses:
                            if assignment[house]['Hobby'] == 'cooking':
                                if assignment[house]['Name'] != 'Alice':
                                    valid = False
                                break

                        # Clue 11: The person whose birthday is in April and the person who enjoys gardening are next to each other.
                        april_house = None
                        gardening_house = None
                        for house in houses:
                            if assignment[house]['Birthday'] == 'april':
                                april_house = int(house)
                            if assignment[house]['Hobby'] == 'gardening':
                                gardening_house = int(house)
                        if april_house is not None and gardening_house is not None:
                            if abs(april_house - gardening_house) != 1:
                                valid = False
                        else:
                            valid = False

                        # Clue 12: The person who paints as a hobby is the person whose birthday is in February.
                        for house in houses:
                            if assignment[house]['Hobby'] == 'painting':
                                if assignment[house]['Birthday'] != 'feb':
                                    valid = False
                                break

                        if valid:
                            # Prepare the solution in the required JSON format
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
                                    "rows": []
                                }
                            }
                            for house in houses:
                                row = [house]
                                row.append(assignment[house]['Name'])
                                row.append(assignment[house]['Hobby'])
                                row.append(assignment[house]['Birthday'])
                                row.append(assignment[house]['Education'])
                                row.append(assignment[house]['Smoothie'])
                                solution["solution"]["rows"].append(row)
                            return json.dumps(solution, indent=2)

    return json.dumps({"solution": {"header": [], "rows": []}})

print(solve_puzzle())