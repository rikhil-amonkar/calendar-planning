import itertools
import json

def main():
    hairs_base = ['black', 'brown', 'red']
    music_base = ['pop', 'jazz', 'rock']
    names_list = ['Eric', 'Arnold', 'Peter', 'Alice']
    
    found = False
    solution_rows = None
    
    for hair_perm in itertools.permutations(hairs_base):
        hair = [hair_perm[0], 'blonde', hair_perm[1], hair_perm[2]]
        if hair[0] == 'brown':
            continue
            
        for music_perm in itertools.permutations(music_base):
            music = ['classical', music_perm[0], music_perm[1], music_perm[2]]
            if music[2] == 'pop':
                continue
                
            for name_perm in itertools.permutations(names_list):
                eric_index = None
                for i, name in enumerate(name_perm):
                    if name == 'Eric':
                        eric_index = i
                        if hair[i] != 'red':
                            break
                else:
                    if eric_index is None:
                        continue
                    if music[eric_index] != 'jazz':
                        continue
                    
                    arnold_index = None
                    valid_arnold = True
                    for i, name in enumerate(name_perm):
                        if name == 'Arnold':
                            arnold_index = i
                            if music[i] != 'rock':
                                valid_arnold = False
                                break
                    if not valid_arnold or arnold_index is None:
                        continue
                    
                    peter_index = None
                    for i, name in enumerate(name_perm):
                        if name == 'Peter':
                            peter_index = i
                    if peter_index is None:
                        continue
                    if peter_index <= arnold_index:
                        continue
                    
                    solution_rows = []
                    for i in range(4):
                        row = [str(i+1), name_perm[i], hair[i], music[i]]
                        solution_rows.append(row)
                    found = True
                    break
            if found:
                break
        if found:
            break
            
    if found:
        header = ["House", "Name", "Hair", "Music"]
        result = {
            "solution": {
                "header": header,
                "rows": solution_rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()