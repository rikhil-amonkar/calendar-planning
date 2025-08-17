import itertools
import json

names = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
heights = ['super tall', 'very tall', 'tall', 'average', 'very short', 'short']
phones = ['oneplus 9', 'google pixel 6', 'samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']

for h_perm in itertools.permutations(['very tall', 'tall', 'average']):
    current_heights = ['super tall', h_perm[0], h_perm[1], h_perm[2], 'very short', 'short']
    
    for p_perm in itertools.permutations(['iphone 13', 'samsung galaxy s21', 'huawei p50', 'xiaomi mi 11']):
        if p_perm[0] == 'samsung galaxy s21':
            continue
        current_phones = [p_perm[0], p_perm[1], p_perm[2], 'google pixel 6', 'oneplus 9', p_perm[3]]
        
        for name_perm in itertools.permutations(['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']):
            # Check Carol's constraints
            carol_index = name_perm.index('Carol')
            if current_heights[carol_index] != 'very tall':
                continue
            if current_phones[carol_index] != 'xiaomi mi 11':
                continue
            
            # Check Arnold's height is 'tall'
            arnold_index = name_perm.index('Arnold')
            if current_heights[arnold_index] != 'tall':
                continue
            
            # Check Bob is directly left of Arnold
            if arnold_index == 0:
                continue
            if name_perm[arnold_index - 1] != 'Bob':
                continue
            
            # Check Peter is left of iPhone 13
            try:
                iphone_13_index = current_phones.index('iphone 13')
            except ValueError:
                continue
            peter_index = name_perm.index('Peter')
            if peter_index >= iphone_13_index:
                continue
            
            # Check Eric is left of house 4
            eric_index = name_perm.index('Eric')
            if (eric_index + 1) >= 4:
                continue
            
            # All constraints passed, build the solution
            solution_rows = []
            for i in range(6):
                house_num = str(i+1)
                name = name_perm[i]
                height = current_heights[i]
                phone = current_phones[i]
                solution_rows.append([house_num, name, height, phone])
            
            # Output JSON
            json_output = {
                "solution": {
                    "header": ["House", "Name", "Height", "PhoneModel"],
                    "rows": solution_rows
                }
            }
            print(json.dumps(json_output))
            exit()