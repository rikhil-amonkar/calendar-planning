import itertools
import json

names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
heights_list = ['very tall', 'tall', 'super tall', 'average', 'very short', 'short']
phones_list = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']

# Generate height permutations with constraints
fixed_heights = ['super tall', None, None, None, 'very short', 'short']
possible_heights = ['very tall', 'tall', 'average']
height_perms = []
for h in itertools.permutations(possible_heights):
    current = fixed_heights.copy()
    current[1] = h[0]
    current[2] = h[1]
    current[3] = h[2]
    height_perms.append(current)

# Generate phone permutations with constraints
fixed_phones = [None, None, None, None, None, None]
fixed_phones[3] = 'google pixel 6'
fixed_phones[4] = 'oneplus 9'
remaining_phones = ['samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
phone_perms = []
for p in itertools.permutations(remaining_phones):
    current = fixed_phones.copy()
    current[0] = p[0]
    current[1] = p[1]
    current[2] = p[2]
    current[5] = p[3]
    phone_perms.append(current)

# Iterate through all possibilities
for name_perm in itertools.permutations(names):
    for h_perm in height_perms:
        # Check Carol's height is 'very tall'
        try:
            i_carol = name_perm.index('Carol')
        except ValueError:
            continue
        if h_perm[i_carol] != 'very tall':
            continue
        # Check Arnold's height is 'tall'
        try:
            i_arnold = name_perm.index('Arnold')
        except ValueError:
            continue
        if h_perm[i_arnold] != 'tall':
            continue
        # Check Bob is directly left of Arnold
        try:
            i_bob = name_perm.index('Bob')
        except ValueError:
            continue
        if i_arnold != i_bob + 1:
            continue
        # Process phone permutations
        for phone_perm in phone_perms:
            # Check Carol's phone is 'xiaomi mi 11'
            if phone_perm[i_carol] != 'xiaomi mi 11':
                continue
            # Check Samsung Galaxy S21 not in first house
            if phone_perm[0] == 'samsung galaxy s21':
                continue
            # Check Peter is to the left of iPhone 13
            try:
                i_peter = name_perm.index('Peter')
            except ValueError:
                continue
            try:
                i_iphone = phone_perm.index('iphone 13')
            except ValueError:
                continue
            if not (i_peter < i_iphone):
                continue
            # Check Eric is to the left of Google Pixel 6 (index 3)
            try:
                i_eric = name_perm.index('Eric')
            except ValueError:
                continue
            if not (i_eric < 3):
                continue
            # All constraints satisfied
            solution_rows = []
            for i in range(6):
                house_num = i + 1
                solution_rows.append([str(house_num), name_perm[i], h_perm[i], phone_perm[i]])
            json_output = {
                "solution": {
                    "header": ["House", "Name", "Height", "PhoneModel"],
                    "rows": solution_rows
                }
            }
            print(json.dumps(json_output, indent=2))
            exit()