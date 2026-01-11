import itertools
import json

# Define the attributes
names = ['Carol', 'Bob', 'Alice', 'Arnold', 'Eric', 'Peter']
phone_models = ['samsung galaxy s21', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9', 'xiaomi mi 11']
nationalities = ['swede', 'chinese', 'norwegian', 'dane', 'german', 'brit']
colors = ['blue', 'red', 'yellow', 'green', 'white', 'purple']

# Define the houses
houses = [1, 2, 3, 4, 5, 6]

# Function to check if a given assignment satisfies all constraints
def is_valid(assignment):
    # Unpack the assignment
    name_assignment, phone_assignment, nationality_assignment, color_assignment = assignment
    
    # Convert to dictionaries for easier access
    name_dict = dict(zip(houses, name_assignment))
    phone_dict = dict(zip(houses, phone_assignment))
    nationality_dict = dict(zip(houses, nationality_assignment))
    color_dict = dict(zip(houses, color_assignment))
    
    # Check each constraint
    if name_dict[3] == 'Carol':
        return False
    if abs(list(nationality_dict.values()).index('dane') - list(nationality_dict.values()).index('brit')) != 2:
        return False
    if color_dict[name_dict.index('Carol')] != 'green':
        return False
    if list(name_dict.values()).index('Arnold') + 1 != list(name_dict.values()).index('Alice'):
        return False
    if nationality_dict[name_dict.index('Alice')] != 'german':
        return False
    if phone_dict[color_dict.index('purple')] != 'oneplus 9':
        return False
    if phone_dict[3] == 'huawei p50':
        return False
    if phone_dict[5] != 'samsung galaxy s21':
        return False
    if list(color_dict.values()).index('white') < list(color_dict.values()).index('red'):
        return False
    if name_dict[phone_dict.index('samsung galaxy s21')] != 'Bob':
        return False
    if nationality_dict[color_dict.index('yellow')] != 'dane':
        return False
    if list(phone_dict.values()).index('samsung galaxy s21') >= list(name_dict.values()).index('Peter'):
        return False
    if color_dict[name_dict.index('Peter')] != 'blue':
        return False
    if nationality_dict[name_dict.index('Peter')] != 'brit':
        return False
    if list(phone_dict.values()).index('samsung galaxy s21') + 1 != list(phone_dict.values()).index('iphone 13'):
        return False
    if nationality_dict[color_dict.index('purple')] != 'norwegian':
        return False
    if phone_dict[nationality_dict.index('chinese')] != 'xiaomi mi 11':
        return False
    
    return True

# Generate all possible assignments
all_assignments = itertools.permutations(names)
all_phone_assignments = itertools.permutations(phone_models)
all_nationality_assignments = itertools.permutations(nationalities)
all_color_assignments = itertools.permutations(colors)

# Try all combinations
for name_assignment in all_assignments:
    for phone_assignment in all_phone_assignments:
        for nationality_assignment in all_nationality_assignments:
            for color_assignment in all_color_assignments:
                assignment = (name_assignment, phone_assignment, nationality_assignment, color_assignment)
                if is_valid(assignment):
                    # Convert to the required JSON format
                    name_dict = dict(zip(houses, name_assignment))
                    phone_dict = dict(zip(houses, phone_assignment))
                    nationality_dict = dict(zip(houses, nationality_assignment))
                    color_dict = dict(zip(houses, color_assignment))
                    
                    solution_rows = []
                    for house in houses:
                        solution_rows.append([
                            str(house),
                            name_dict[house],
                            phone_dict[house],
                            nationality_dict[house],
                            color_dict[house]
                        ])
                    
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "PhoneModel", "Nationality", "Color"],
                            "rows": solution_rows
                        }
                    }
                    
                    print(json.dumps(solution, indent=2))
                    exit(0)