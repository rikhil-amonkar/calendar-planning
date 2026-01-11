import itertools
import json

def is_valid_solution(solution):
    # Unpack the solution into lists for easier access
    names = [house['Name'] for house in solution]
    colors = [house['Color'] for house in solution]
    phones = [house['PhoneModel'] for house in solution]
    occupations = [house['Occupation'] for house in solution]

    # Check all constraints
    # 1. The person who is an engineer is somewhere to the right of the person who is a lawyer.
    if occupations.index('engineer') <= occupations.index('lawyer'):
        return False

    # 2. Bob is in the second house.
    if names[1] != 'Bob':
        return False

    # 3. The person who uses a Samsung Galaxy S21 is the person who is a doctor.
    if phones.index('samsung galaxy s21') != occupations.index('doctor'):
        return False

    # 4. The person who is a doctor is the person who loves blue.
    if occupations.index('doctor') != colors.index('blue'):
        return False

    # 5. The person whose favorite color is green is not in the fifth house.
    if colors[4] == 'green':
        return False

    # 6. The person who is a lawyer is the person who uses a OnePlus 9.
    if occupations.index('lawyer') != phones.index('oneplus 9'):
        return False

    # 7. The person who loves blue is directly left of the person whose favorite color is red.
    if colors.index('blue') + 1 != colors.index('red'):
        return False

    # 8. The person who is a lawyer is somewhere to the right of the person who uses a Samsung Galaxy S21.
    if occupations.index('lawyer') <= phones.index('samsung galaxy s21'):
        return False

    # 9. There is one house between the person who uses a Google Pixel 6 and the person who uses a Huawei P50.
    idx_pixel = phones.index('google pixel 6')
    idx_huawei = phones.index('huawei p50')
    if abs(idx_pixel - idx_huawei) != 2:
        return False

    # 10. Arnold is the person who is an engineer.
    if names[occupations.index('engineer')] != 'Arnold':
        return False

    # 11. Alice is the person who loves yellow.
    if names[colors.index('yellow')] != 'Alice':
        return False

    # 12. The person who uses a Google Pixel 6 is Eric.
    if names[phones.index('google pixel 6')] != 'Eric':
        return False

    # 13. The person who uses a Google Pixel 6 is the person who is a teacher.
    if phones.index('google pixel 6') != occupations.index('teacher'):
        return False

    # 14. The person whose favorite color is red is somewhere to the right of the person who is a teacher.
    if colors.index('red') <= occupations.index('teacher'):
        return False

    return True

def solve_puzzle():
    # Define the possible values for each attribute
    names = ['Bob', 'Eric', 'Arnold', 'Alice', 'Peter']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    phones = ['huawei p50', 'samsung galaxy s21', 'oneplus 9', 'iphone 13', 'google pixel 6']
    occupations = ['artist', 'teacher', 'doctor', 'engineer', 'lawyer']

    # Generate all possible permutations for each attribute
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(colors)) * \
                       list(itertools.permutations(phones)) * \
                       list(itertools.permutations(occupations))

    # Iterate over all permutations and find the valid solution
    for name_perm in itertools.permutations(names):
        for color_perm in itertools.permutations(colors):
            for phone_perm in itertools.permutations(phones):
                for occupation_perm in itertools.permutations(occupations):
                    solution = [
                        {'Name': name_perm[0], 'Color': color_perm[0], 'PhoneModel': phone_perm[0], 'Occupation': occupation_perm[0]},
                        {'Name': name_perm[1], 'Color': color_perm[1], 'PhoneModel': phone_perm[1], 'Occupation': occupation_perm[1]},
                        {'Name': name_perm[2], 'Color': color_perm[2], 'PhoneModel': phone_perm[2], 'Occupation': occupation_perm[2]},
                        {'Name': name_perm[3], 'Color': color_perm[3], 'PhoneModel': phone_perm[3], 'Occupation': occupation_perm[3]},
                        {'Name': name_perm[4], 'Color': color_perm[4], 'PhoneModel': phone_perm[4], 'Occupation': occupation_perm[4]}
                    ]
                    if is_valid_solution(solution):
                        return solution

# Solve the puzzle
solution = solve_puzzle()

# Format the solution as JSON
json_solution = {
    "solution": {
        "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
        "rows": [
            [str(i+1), house['Name'], house['Color'], house['PhoneModel'], house['Occupation']] for i, house in enumerate(solution)
        ]
    }
}

# Output the solution as JSON
print(json.dumps(json_solution, indent=2))