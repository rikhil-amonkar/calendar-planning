import json
from itertools import permutations

def solve_puzzle():
    # Define all possible options for each attribute
    names = ['Peter', 'Eric', 'Alice', 'Arnold']
    educations = ['bachelor', 'high school', 'associate', 'master']
    music_genres = ['jazz', 'rock', 'pop', 'classical']
    colors = ['green', 'red', 'yellow', 'white']
    flowers = ['lilies', 'carnations', 'daffodils', 'roses']
    houses = ['1', '2', '3', '4']

    # Generate all possible permutations for each attribute
    for name_perm in permutations(names):
        for edu_perm in permutations(educations):
            for music_perm in permutations(music_genres):
                for color_perm in permutations(colors):
                    for flower_perm in permutations(flowers):
                        # Create a list of houses with their attributes
                        solution = [
                            {
                                'House': house,
                                'Name': name,
                                'education': edu,
                                'music genre': music,
                                'color': color,
                                'flower': flower
                            }
                            for house, name, edu, music, color, flower in zip(
                                houses, name_perm, edu_perm, music_perm, color_perm, flower_perm
                            )
                        ]

                        # Check all constraints
                        valid = True

                        # Constraint 1: bachelor's degree loves daffodils
                        for house in solution:
                            if house['education'] == 'bachelor' and house['flower'] != 'daffodils':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 2: carnations not in first house
                        if solution[0]['flower'] == 'carnations':
                            valid = False
                        if not valid:
                            continue

                        # Constraint 3: master's degree is Alice
                        for house in solution:
                            if house['education'] == 'master' and house['Name'] != 'Alice':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 4: master's degree is directly left of classical music
                        master_pos = None
                        classical_pos = None
                        for i, house in enumerate(solution):
                            if house['education'] == 'master':
                                master_pos = i
                            if house['music genre'] == 'classical':
                                classical_pos = i
                        if master_pos is None or classical_pos is None or classical_pos - master_pos != 1:
                            valid = False
                        if not valid:
                            continue

                        # Constraint 5: Eric is not in the second house
                        if solution[1]['Name'] == 'Eric':
                            valid = False
                        if not valid:
                            continue

                        # Constraint 6: Arnold is not in the third house
                        if solution[2]['Name'] == 'Arnold':
                            valid = False
                        if not valid:
                            continue

                        # Constraint 7: yellow is directly left of roses
                        yellow_pos = None
                        roses_pos = None
                        for i, house in enumerate(solution):
                            if house['color'] == 'yellow':
                                yellow_pos = i
                            if house['flower'] == 'roses':
                                roses_pos = i
                        if yellow_pos is None or roses_pos is None or roses_pos - yellow_pos != 1:
                            valid = False
                        if not valid:
                            continue

                        # Constraint 8: pop music is in the second house
                        if solution[1]['music genre'] != 'pop':
                            valid = False
                        if not valid:
                            continue

                        # Constraint 9: associate's degree not in fourth house
                        if solution[3]['education'] == 'associate':
                            valid = False
                        if not valid:
                            continue

                        # Constraint 10: carnations not in fourth house
                        if solution[3]['flower'] == 'carnations':
                            valid = False
                        if not valid:
                            continue

                        # Constraint 11: red is directly left of white
                        red_pos = None
                        white_pos = None
                        for i, house in enumerate(solution):
                            if house['color'] == 'red':
                                red_pos = i
                            if house['color'] == 'white':
                                white_pos = i
                        if red_pos is None or white_pos is None or white_pos - red_pos != 1:
                            valid = False
                        if not valid:
                            continue

                        # Constraint 12: red color loves rock music
                        for house in solution:
                            if house['color'] == 'red' and house['music genre'] != 'rock':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 13: Arnold loves yellow
                        for house in solution:
                            if house['Name'] == 'Arnold' and house['color'] != 'yellow':
                                valid = False
                                break
                            if house['color'] == 'yellow' and house['Name'] != 'Arnold':
                                valid = False
                                break
                        if not valid:
                            continue

                        # Constraint 14: daffodils lover loves yellow
                        for house in solution:
                            if house['flower'] == 'daffodils' and house['color'] != 'yellow':
                                valid = False
                                break
                            if house['color'] == 'yellow' and house['flower'] != 'daffodils':
                                valid = False
                                break
                        if not valid:
                            continue

                        if valid:
                            # Prepare the output
                            output = {
                                "solution": {
                                    "header": ["House", "Name", "education", "music genre", "color", "flower"],
                                    "rows": []
                                }
                            }
                            for house in solution:
                                output["solution"]["rows"].append([
                                    house['House'],
                                    house['Name'],
                                    house['education'],
                                    house['music genre'],
                                    house['color'],
                                    house['flower']
                                ])
                            return output

    return {"solution": {"header": [], "rows": []}}

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))