import itertools
import json

def main():
    names = ['Eric', 'Arnold', 'Peter']
    books = ['mystery', 'science fiction', 'romance']
    vacs = ['mountain', 'beach', 'city']
    
    for n_perm in itertools.permutations(names):
        for b_perm in itertools.permutations(books):
            for v_perm in itertools.permutations(vacs):
                assignment = [
                    [n_perm[0], b_perm[0], v_perm[0]],
                    [n_perm[1], b_perm[1], v_perm[1]],
                    [n_perm[2], b_perm[2], v_perm[2]]
                ]
                
                # Check constraint 3: Peter has vacation 'city'
                city_index = None
                for idx, house in enumerate(assignment):
                    if house[2] == 'city':
                        city_index = idx
                        if house[0] != 'Peter':
                            break
                else:
                    if city_index is not None:
                        # We found a city and it was Peter, now check other constraints
                        pass
                    else:
                        continue
                if city_index is None or assignment[city_index][0] != 'Peter':
                    continue
                    
                # Check constraint 5: beach vacation has science fiction book
                beach_index = None
                for idx, house in enumerate(assignment):
                    if house[2] == 'beach':
                        beach_index = idx
                        if house[1] != 'science fiction':
                            break
                else:
                    if beach_index is not None:
                        pass
                    else:
                        continue
                if beach_index is None or assignment[beach_index][1] != 'science fiction':
                    continue
                    
                # Check constraint 1: Eric directly left of Arnold
                name_list = [house[0] for house in assignment]
                if 'Eric' not in name_list or 'Arnold' not in name_list:
                    continue
                eric_index = name_list.index('Eric')
                arnold_index = name_list.index('Arnold')
                if eric_index + 1 != arnold_index:
                    continue
                    
                # Check constraint 2: Peter is to the right of beach vacation person
                if city_index <= beach_index:
                    continue
                    
                # Check constraint 4: mystery book left of beach vacation
                book_list = [house[1] for house in assignment]
                if 'mystery' not in book_list:
                    continue
                mystery_index = book_list.index('mystery')
                if mystery_index >= beach_index:
                    continue
                    
                # Found a valid solution
                solution_rows = []
                for i, house in enumerate(assignment):
                    solution_rows.append([str(i+1), house[0], house[1], house[2]])
                    
                result = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre", "Vacation"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(result))
                return
                
    # If no solution found, output an empty solution (though puzzle should have one)
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation"],
            "rows": []
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()