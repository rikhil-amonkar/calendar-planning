import itertools
import json

def main():
    names_all = ['Alice', 'Arnold', 'Peter', 'Eric']
    hairs_all = ['black', 'blonde', 'brown', 'red']
    
    remaining_names = [n for n in names_all if n not in ['Alice', 'Arnold']]
    solution_rows = None
    
    for p in itertools.permutations(remaining_names):
        name_assignment = ['Alice', 'Arnold'] + list(p)
        if name_assignment[3] == 'Eric':
            continue
        if name_assignment[2] != 'Eric':
            continue
        remaining_hairs = [h for h in hairs_all if h not in ['brown', 'blonde']]
        if set(remaining_hairs) != set(['black', 'red']):
            continue
        hair_assignment = ['red', 'black', 'brown', 'blonde']
        solution_rows = [
            ['1', name_assignment[0], hair_assignment[0]],
            ['2', name_assignment[1], hair_assignment[1]],
            ['3', name_assignment[2], hair_assignment[2]],
            ['4', name_assignment[3], hair_assignment[3]]
        ]
        break
    
    if solution_rows is None:
        result = {"solution": {"header": [], "rows": []}}
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "Hair"],
                "rows": solution_rows
            }
        }
    
    print(json.dumps(result))

if __name__ == '__main__':
    main()