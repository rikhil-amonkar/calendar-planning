import itertools
import json

def main():
    names_list = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold', 'Carol']
    remaining_heights = ['very tall', 'tall', 'average']
    remaining_phones = ['samsung galaxy s21', 'iphone 13', 'huawei p50', 'xiaomi mi 11']
    
    found_solution = False
    solution_data = None
    
    for height_perm in itertools.permutations(remaining_heights):
        heights = ['super tall'] + list(height_perm) + ['very short', 'short']
        
        for name_perm in itertools.permutations(names_list):
            names = list(name_perm)
            
            if 'Eric' not in names[0:3]:
                continue
                
            carol_index = names.index('Carol') if 'Carol' in names else -1
            if carol_index == -1:
                continue
            if heights[carol_index] != 'very tall':
                continue
                
            if 'Arnold' not in names:
                continue
            arnold_index = names.index('Arnold')
            if heights[arnold_index] != 'tall':
                continue
                
            if arnold_index == 0:
                continue
            if names[arnold_index-1] != 'Bob':
                continue
                
            for phone_perm in itertools.permutations(remaining_phones):
                phones = [None] * 6
                phones[0] = phone_perm[0]
                phones[1] = phone_perm[1]
                phones[2] = phone_perm[2]
                phones[3] = 'google pixel 6'
                phones[4] = 'oneplus 9'
                phones[5] = phone_perm[3]
                
                if phones[0] == 'samsung galaxy s21':
                    continue
                    
                if phones[carol_index] != 'xiaomi mi 11':
                    continue
                    
                if 'Peter' not in names:
                    continue
                peter_index = names.index('Peter')
                if 'iphone 13' not in phones:
                    continue
                iphone_index = phones.index('iphone 13')
                if peter_index >= iphone_index:
                    continue
                    
                solution_rows = []
                for i in range(6):
                    solution_rows.append([str(i+1), names[i], heights[i], phones[i]])
                
                solution_data = {
                    "header": ["House", "Name", "Height", "Phone"],
                    "rows": solution_rows
                }
                found_solution = True
                break
            if found_solution:
                break
        if found_solution:
            break
            
    if solution_data:
        result = {"solution": solution_data}
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == '__main__':
    main()