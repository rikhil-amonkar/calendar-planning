import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']

    for name_perm in itertools.permutations(names):
        if name_perm[1] != 'Bob':
            continue
        for color_perm in itertools.permutations(colors):
            if color_perm[4] == 'green' or color_perm[3] != 'blue' or color_perm[4] != 'red':
                continue
            for phone_perm in itertools.permutations(phones):
                if (phone_perm[name_perm.index('Eric')] != 'google pixel 6' or
                    phone_perm[name_perm.index('doctor')] != 'samsung galaxy s21' or
                    phone_perm[name_perm.index('lawyer')] != 'oneplus 9'):
                    continue
                for occupation_perm in itertools.permutations(occupations):
                    if (occupation_perm[name_perm.index('Arnold')] != 'engineer' or
                        occupation_perm[name_perm.index('Alice')] != 'yellow' or
                        occupation_perm[name_perm.index('Eric')] != 'teacher' or
                        occupation_perm[name_perm.index('doctor')] != 'blue' or
                        occupation_perm[name_perm.index('lawyer')] > occupation_perm[name_perm.index('samsung galaxy s21')] or
                        occupation_perm[name_perm.index('engineer')] <= occupation_perm[name_perm.index('lawyer')] or
                        abs(phone_perm.index('google pixel 6') - phone_perm.index('huawei p50')) != 2 or
                        color_perm.index('blue') + 1 != color_perm.index('red') or
                        occupation_perm.index('teacher') >= occupation_perm.index('red')):
                        continue
                    solution = []
                    for house in range(5):
                        solution.append([
                            str(house + 1),
                            name_perm[house],
                            color_perm[house],
                            phone_perm[house],
                            occupation_perm[house]
                        ])
                    return json.dumps({
                        "solution": {
                            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
                            "rows": solution
                        }
                    })

print(solve_puzzle())