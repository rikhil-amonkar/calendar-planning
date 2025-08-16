import itertools
import json

def main():
    names_all = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
    children_remaining = ['Timothy', 'Meredith', 'Samantha']
    child_positions = [0, 3, 4]  # Houses 1, 4, 5 (0-indexed indices)
    
    found = False
    solution_rows = None
    
    for child_perm in itertools.permutations(children_remaining):
        child_list = [None] * 5
        child_list[1] = 'Fred'
        child_list[2] = 'Bella'
        for idx, c in zip(child_positions, child_perm):
            child_list[idx] = c
        
        for name_perm in itertools.permutations(names_all):
            name_list = list(name_perm)
            
            if name_list[2] == 'Eric' or name_list[2] == 'Bob':
                continue
                
            try:
                samantha_child_index = child_list.index('Samantha')
            except ValueError:
                continue
                
            try:
                bob_index = name_list.index('Bob')
            except ValueError:
                continue
            if bob_index >= samantha_child_index:
                continue
                
            try:
                timothy_child_index = child_list.index('Timothy')
            except ValueError:
                continue
            if timothy_child_index >= samantha_child_index:
                continue
                
            try:
                alice_index = name_list.index('Alice')
            except ValueError:
                continue
            if abs(alice_index - samantha_child_index) != 2:
                continue
                
            try:
                peter_index = name_list.index('Peter')
            except ValueError:
                continue
            if samantha_child_index >= peter_index:
                continue
                
            solution_rows = []
            for i in range(5):
                solution_rows.append([str(i+1), name_list[i], child_list[i]])
            found = True
            break
            
        if found:
            break
            
    if found:
        result = {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": solution_rows
            }
        }
        print(json.dumps(result))
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": []
            }
        }
        print(json.dumps(result))

if __name__ == "__main__":
    main()