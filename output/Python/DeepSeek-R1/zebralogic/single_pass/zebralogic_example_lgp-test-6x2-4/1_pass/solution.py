import itertools
import json

def main():
    names = ['Alice', 'Arnold', 'Carol', 'Peter', 'Bob', 'Eric']
    phones = ['huawei p50', 'iphone 13', 'xiaomi mi 11', 'oneplus 9', 'samsung galaxy s21', 'google pixel 6']
    
    remaining_names = ['Alice', 'Carol', 'Peter', 'Bob']
    remaining_phones = ['iphone 13', 'samsung galaxy s21', 'google pixel 6']
    
    solution_found = None
    
    for n_perm in itertools.permutations(remaining_names):
        for p_perm in itertools.permutations(remaining_phones):
            assignment = [None] * 6
            assignment[0] = ('Eric', 'huawei p50')
            assignment[1] = (n_perm[0], p_perm[0])
            assignment[2] = (n_perm[1], 'xiaomi mi 11')
            assignment[3] = (n_perm[2], p_perm[1])
            assignment[4] = (n_perm[3], p_perm[2])
            assignment[5] = ('Arnold', 'oneplus 9')
            
            valid = True
            for i in range(6):
                if assignment[i][1] == 'iphone 13':
                    if assignment[i][0] != 'Alice':
                        valid = False
                        break
            if not valid:
                continue
                
            if assignment[1][1] == 'google pixel 6' or assignment[1][1] == 'iphone 13':
                valid = False
            if not valid:
                continue
                
            alice_index = None
            carol_index = None
            for idx in range(6):
                if assignment[idx][0] == 'Alice':
                    alice_index = idx
                elif assignment[idx][0] == 'Carol':
                    carol_index = idx
            if alice_index is None or carol_index is None or alice_index >= carol_index:
                continue
                
            bob_index = None
            for idx in range(6):
                if assignment[idx][0] == 'Bob':
                    bob_index = idx
            if bob_index is None:
                continue
            if abs(bob_index - carol_index) != 2:
                continue
                
            solution_found = assignment
            break
        if solution_found is not None:
            break
            
    if solution_found is None:
        print(json.dumps({"solution": {}}))
        return
        
    output = {
        "solution": {
            "header": ["House", "Name", "Phone Model"],
            "rows": []
        }
    }
    
    for i in range(6):
        house_number = str(i+1)
        name = solution_found[i][0]
        phone = solution_found[i][1]
        output["solution"]["rows"].append([house_number, name, phone])
        
    print(json.dumps(output))
    
if __name__ == "__main__":
    main()