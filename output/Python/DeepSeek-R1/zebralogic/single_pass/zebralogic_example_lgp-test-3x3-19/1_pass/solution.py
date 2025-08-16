import itertools
import json

def main():
    names = ['Eric', 'Arnold', 'Peter']
    smoothies = ['desert', 'watermelon', 'cherry']
    book_genres = ['science fiction', 'romance', 'mystery']
    
    found = False
    solution_data = None
    
    for n_perm in itertools.permutations(names):
        if n_perm[0] != 'Peter':
            continue
            
        for s_perm in itertools.permutations(smoothies):
            for b_perm in itertools.permutations(book_genres):
                if b_perm[0] == 'science fiction':
                    continue
                    
                mystery_index = None
                for idx, genre in enumerate(b_perm):
                    if genre == 'mystery':
                        mystery_index = idx
                        break
                if mystery_index is None:
                    continue
                    
                if n_perm[mystery_index] != 'Arnold':
                    continue
                    
                cherry_index = None
                for idx, sm in enumerate(s_perm):
                    if sm == 'cherry':
                        cherry_index = idx
                        break
                if cherry_index is None or cherry_index >= mystery_index:
                    continue
                    
                desert_index = None
                for idx, sm in enumerate(s_perm):
                    if sm == 'desert':
                        desert_index = idx
                        break
                if desert_index is None or desert_index != mystery_index - 1:
                    continue
                    
                rows = []
                for i in range(3):
                    rows.append([str(i+1), n_perm[i], s_perm[i], b_perm[i]])
                    
                solution_data = {
                    "solution": {
                        "header": ["House", "Name", "Smoothie", "BookGenre"],
                        "rows": rows
                    }
                }
                found = True
                break
            if found:
                break
        if found:
            break
            
    if not found:
        solution_data = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "BookGenre"],
                "rows": []
            }
        }
        
    print(json.dumps(solution_data))

if __name__ == '__main__':
    main()