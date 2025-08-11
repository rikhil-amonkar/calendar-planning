import itertools
import json

def main():
    names = ['Arnold', 'Eric', 'Peter', 'Alice']
    occupations = ['doctor', 'engineer', 'artist', 'teacher']
    
    for name_perm in itertools.permutations(names):
        if name_perm[0] == 'Peter':
            continue
            
        eric_index = None
        peter_index = None
        for idx, name in enumerate(name_perm):
            if name == 'Eric':
                eric_index = idx
            elif name == 'Peter':
                peter_index = idx
                
        if eric_index is None or peter_index is None:
            continue
            
        if abs(eric_index - peter_index) != 3:
            continue
            
        for occ_perm in itertools.permutations(occupations):
            if occ_perm[3] != 'teacher':
                continue
                
            alice_index = None
            for idx, name in enumerate(name_perm):
                if name == 'Alice':
                    alice_index = idx
                    break
            if alice_index is None:
                continue
                
            if occ_perm[alice_index] != 'artist':
                continue
                
            doctor_index = None
            for idx, occ in enumerate(occ_perm):
                if occ == 'doctor':
                    doctor_index = idx
                    break
            if doctor_index is None:
                continue
                
            if abs(doctor_index - alice_index) != 2:
                continue
                
            solution = {
                "header": ["House", "Name", "Occupation"],
                "rows": []
            }
            for i in range(4):
                house_num = str(i+1)
                name_val = name_perm[i]
                occ_val = occ_perm[i]
                solution["rows"].append([house_num, name_val, occ_val])
                
            print(json.dumps({"solution": solution}))
            return
            
    print(json.dumps({"solution": None}))

if __name__ == '__main__':
    main()