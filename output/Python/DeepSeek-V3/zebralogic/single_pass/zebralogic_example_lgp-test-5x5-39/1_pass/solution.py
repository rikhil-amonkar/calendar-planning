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

    # Initialize solution structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
            "rows": []
        }
    }

    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for month_perm in permutations(months):
            for mother_perm in permutations(mothers):
                for occ_perm in permutations(occupations):
                    for hair_perm in permutations(hair_colors):
                        # Create a dictionary for each house
                        assignment = []
                        valid = True
                        for i in range(5):
                            house = {
                                "House": str(i+1),
                                "Name": name_perm[i],
                                "Birthday": month_perm[i],
                                "Mother": mother_perm[i],
                                "Occupation": occ_perm[i],
                                "HairColor": hair_perm[i]
                            }
                            assignment.append(house)

                        # Check all constraints
                        # Constraint 1: mar in house 5
                        if assignment[4]["Birthday"] != 'mar':
                            continue
                        # Constraint 2: feb in house 1
                        if assignment[0]["Birthday"] != 'feb':
                            continue
                        # Constraint 3: doctor is Eric
                        for house in assignment:
                            if house["Occupation"] == 'doctor' and house["Name"] != 'Eric':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 4: mother Janelle in house 3
                        if assignment[2]["Mother"] != 'Janelle':
                            continue
                        # Constraint 5: artist has brown hair
                        for house in assignment:
                            if house["Occupation"] == 'artist' and house["HairColor"] != 'brown':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 6: artist in house 4
                        if assignment[3]["Occupation"] != 'artist':
                            continue
                        # Constraint 7: Penny left of black hair
                        penny_pos = None
                        black_pos = None
                        for i in range(5):
                            if assignment[i]["Mother"] == 'Penny':
                                penny_pos = i
                            if assignment[i]["HairColor"] == 'black':
                                black_pos = i
                        if penny_pos is None or black_pos is None or penny_pos >= black_pos:
                            continue
                        # Constraint 8: Peter has black hair
                        for house in assignment:
                            if house["Name"] == 'Peter' and house["HairColor"] != 'black':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 9: gray hair is teacher
                        for house in assignment:
                            if house["HairColor"] == 'gray' and house["Occupation"] != 'teacher':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 10: Alice's mother is Kailyn
                        for house in assignment:
                            if house["Name"] == 'Alice' and house["Mother"] != 'Kailyn':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 11: Arnold right of sept
                        arnold_pos = None
                        sept_pos = None
                        for i in range(5):
                            if assignment[i]["Name"] == 'Arnold':
                                arnold_pos = i
                            if assignment[i]["Birthday"] == 'sept':
                                sept_pos = i
                        if arnold_pos is None or sept_pos is None or arnold_pos <= sept_pos:
                            continue
                        # Constraint 12: brown hair is jan birthday
                        for house in assignment:
                            if house["HairColor"] == 'brown' and house["Birthday"] != 'jan':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 13: Arnold has blonde hair
                        for house in assignment:
                            if house["Name"] == 'Arnold' and house["HairColor"] != 'blonde':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 14: mother Holly has black hair
                        for house in assignment:
                            if house["Mother"] == 'Holly' and house["HairColor"] != 'black':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 15: Peter is lawyer
                        for house in assignment:
                            if house["Name"] == 'Peter' and house["Occupation"] != 'lawyer':
                                valid = False
                                break
                        if not valid:
                            continue
                        # Constraint 16: sept left of Kailyn
                        kailyn_pos = None
                        for i in range(5):
                            if assignment[i]["Mother"] == 'Kailyn':
                                kailyn_pos = i
                        if sept_pos is None or kailyn_pos is None or sept_pos >= kailyn_pos:
                            continue
                        # Constraint 17: Alice has gray hair
                        for house in assignment:
                            if house["Name"] == 'Alice' and house["HairColor"] != 'gray':
                                valid = False
                                break
                        if not valid:
                            continue

                        # If all constraints passed, format the solution
                        rows = []
                        for house in assignment:
                            row = [
                                house["House"],
                                house["Name"],
                                house["Birthday"],
                                house["Mother"],
                                house["Occupation"],
                                house["HairColor"]
                            ]
                            rows.append(row)
                        solution["solution"]["rows"] = rows
                        return json.dumps(solution, indent=2)

    return json.dumps(solution, indent=2)

print(solve_puzzle())