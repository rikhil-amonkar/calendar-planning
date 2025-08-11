import itertools
import json

def satisfies_constraints(houses):
    # Constraint 1: Pall Mall cigar is Peter.
    for i in range(3):
        if houses[i][1] == 'pall mall':
            if houses[i][0] != 'Peter':
                return False
            break
    else:
        return False

    # Constraint 2: milk directly left of high school
    if houses[0][4] == 'milk':
        if houses[1][3] != 'high school':
            return False
    elif houses[1][4] == 'milk':
        if houses[2][3] != 'high school':
            return False
    else:
        return False

    # Constraint 3: Eric is tea drinker
    for i in range(3):
        if houses[i][0] == 'Eric':
            if houses[i][4] != 'tea':
                return False
            break
    else:
        return False

    # Constraint 4: Arnold and Prince adjacent
    arnold_index = None
    prince_index = None
    for i in range(3):
        if houses[i][0] == 'Arnold':
            arnold_index = i
        if houses[i][1] == 'prince':
            prince_index = i
    if arnold_index is None or prince_index is None:
        return False
    if abs(arnold_index - prince_index) != 1:
        return False

    # Constraint 5: gardening left of prince
    gardening_index = None
    for i in range(3):
        if houses[i][2] == 'gardening':
            gardening_index = i
            break
    else:
        return False
    if gardening_index >= prince_index:
        return False

    # Constraint 6: milk has associate degree
    for i in range(3):
        if houses[i][4] == 'milk':
            if houses[i][3] != 'associate':
                return False
            break
    else:
        return False

    # Constraint 7: bachelor directly left of photography
    if houses[0][3] == 'bachelor':
        if houses[1][2] != 'photography':
            return False
    elif houses[1][3] == 'bachelor':
        if houses[2][2] != 'photography':
            return False
    else:
        return False

    return True

def main():
    names = ['Eric', 'Peter', 'Arnold']
    cigars = ['blue master', 'prince', 'pall mall']
    hobbies = ['photography', 'gardening', 'cooking']
    educations = ['high school', 'associate', 'bachelor']
    drinks = ['tea', 'milk', 'water']

    perms_names = list(itertools.permutations(names))
    perms_cigars = list(itertools.permutations(cigars))
    perms_hobbies = list(itertools.permutations(hobbies))
    perms_educations = list(itertools.permutations(educations))
    perms_drinks = list(itertools.permutations(drinks))

    for n in perms_names:
        for c in perms_cigars:
            for h in perms_hobbies:
                for e in perms_educations:
                    for d in perms_drinks:
                        houses = []
                        for i in range(3):
                            house = (n[i], c[i], h[i], e[i], d[i])
                            houses.append(house)
                        if satisfies_constraints(houses):
                            header = ["House", "name", "favorite cigar", "hobby", "level of education", "favorite drink"]
                            rows = []
                            for idx, house in enumerate(houses):
                                row = [str(idx+1), house[0], house[1], house[2], house[3], house[4]]
                                rows.append(row)
                            sol = {
                                "solution": {
                                    "header": header,
                                    "rows": rows
                                }
                            }
                            print(json.dumps(sol))
                            return
    print(json.dumps({"error": "No solution found"}))
    exit(1)

if __name__ == "__main__":
    main()