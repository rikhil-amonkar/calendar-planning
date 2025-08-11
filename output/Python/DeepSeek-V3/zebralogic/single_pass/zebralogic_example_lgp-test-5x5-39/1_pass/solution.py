import json
from itertools import permutations

def solve_puzzle():
    # Define all possible categories and options
    houses = ['1', '2', '3', '4', '5']
    names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold']
    months = ['mar', 'april', 'sept', 'feb', 'jan']
    mothers = ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya']
    occupations = ['engineer', 'doctor', 'lawyer', 'artist', 'teacher']
    hair_colors = ['red', 'blonde', 'black', 'gray', 'brown']

    # Initialize the solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "birthday month", "mother's name", "occupation", "hair color"],
            "rows": []
        }
    }

    # Generate all possible permutations for each category
    for name_order in permutations(names):
        for month_order in permutations(months):
            for mother_order in permutations(mothers):
                for occupation_order in permutations(occupations):
                    for hair_order in permutations(hair_colors):
                        # Create a list of houses with their attributes
                        houses_data = []
                        valid = True
                        for i in range(5):
                            house = {
                                "House": str(i+1),
                                "Name": name_order[i],
                                "birthday month": month_order[i],
                                "mother's name": mother_order[i],
                                "occupation": occupation_order[i],
                                "hair color": hair_order[i]
                            }
                            houses_data.append(house)

                        # Apply the constraints
                        # Constraint 1: March is in house 5
                        if houses_data[4]["birthday month"] != "mar":
                            valid = False
                            continue
                        # Constraint 2: February is in house 1
                        if houses_data[0]["birthday month"] != "feb":
                            valid = False
                            continue
                        # Constraint 3: Eric is the doctor
                        for house in houses_data:
                            if house["Name"] == "Eric" and house["occupation"] != "doctor":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 4: Janelle is mother in house 3
                        if houses_data[2]["mother's name"] != "Janelle":
                            valid = False
                            continue
                        # Constraint 5: artist has brown hair
                        for house in houses_data:
                            if house["occupation"] == "artist" and house["hair color"] != "brown":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 6: artist is in house 4
                        if houses_data[3]["occupation"] != "artist":
                            valid = False
                            continue
                        # Constraint 7: Penny is left of black hair
                        penny_pos = None
                        black_hair_pos = None
                        for i, house in enumerate(houses_data):
                            if house["mother's name"] == "Penny":
                                penny_pos = i
                            if house["hair color"] == "black":
                                black_hair_pos = i
                        if penny_pos is None or black_hair_pos is None or penny_pos >= black_hair_pos:
                            valid = False
                            continue
                        # Constraint 8: Peter has black hair
                        for house in houses_data:
                            if house["Name"] == "Peter" and house["hair color"] != "black":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 9: gray hair is teacher
                        for house in houses_data:
                            if house["hair color"] == "gray" and house["occupation"] != "teacher":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 10: Alice's mother is Kailyn
                        for house in houses_data:
                            if house["Name"] == "Alice" and house["mother's name"] != "Kailyn":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 11: Arnold is right of sept birthday
                        sept_pos = None
                        arnold_pos = None
                        for i, house in enumerate(houses_data):
                            if house["birthday month"] == "sept":
                                sept_pos = i
                            if house["Name"] == "Arnold":
                                arnold_pos = i
                        if sept_pos is None or arnold_pos is None or arnold_pos <= sept_pos:
                            valid = False
                            continue
                        # Constraint 12: brown hair is jan birthday
                        for house in houses_data:
                            if house["hair color"] == "brown" and house["birthday month"] != "jan":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 13: Arnold has blonde hair
                        for house in houses_data:
                            if house["Name"] == "Arnold" and house["hair color"] != "blonde":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 14: Holly is mother of black hair
                        for house in houses_data:
                            if house["hair color"] == "black" and house["mother's name"] != "Holly":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 15: Peter is lawyer
                        for house in houses_data:
                            if house["Name"] == "Peter" and house["occupation"] != "lawyer":
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 16: sept is left of Kailyn (Alice's mother)
                        alice_pos = None
                        for i, house in enumerate(houses_data):
                            if house["Name"] == "Alice":
                                alice_pos = i
                        if sept_pos is None or alice_pos is None or sept_pos >= alice_pos:
                            valid = False
                            continue
                        # Constraint 17: Alice has gray hair
                        for house in houses_data:
                            if house["Name"] == "Alice" and house["hair color"] != "gray":
                                valid = False
                                break
                        if not valid:
                            continue

                        # If all constraints are satisfied, build the solution
                        if valid:
                            rows = []
                            for house in houses_data:
                                row = [
                                    house["House"],
                                    house["Name"],
                                    house["birthday month"],
                                    house["mother's name"],
                                    house["occupation"],
                                    house["hair color"]
                                ]
                                rows.append(row)
                            solution["solution"]["rows"] = rows
                            return json.dumps(solution, indent=2)

    return json.dumps(solution, indent=2)

print(solve_puzzle())