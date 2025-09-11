import itertools
import json

names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
book_genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']

solution_found = False

for name_perm in itertools.permutations(names):
    if name_perm[2] != 'Eric':
        continue
    try:
        A = name_perm.index('Alice')
        C = name_perm.index('Carol')
        B = name_perm.index('Bob')
    except ValueError:
        continue
    if abs(B - C) != 1:
        continue
    if B == 4:
        continue
    
    remaining_occs = [occ for occ in occupations if occ not in ['doctor', 'lawyer']]
    remaining_indices = [i for i in range(6) if i != 0 and i != A]
    
    for occs in itertools.permutations(remaining_occs):
        occ_perm = [None] * 6
        occ_perm[0] = 'doctor'
        occ_perm[A] = 'lawyer'
        for i, idx in enumerate(remaining_indices):
            occ_perm[idx] = occs[i]
        
        if A - 1 < 0 or occ_perm[A - 1] != 'nurse':
            continue
        
        Arnold_idx = name_perm.index('Arnold')
        try:
            engineer_idx = occ_perm.index('engineer')
        except ValueError:
            continue
        if Arnold_idx >= engineer_idx:
            continue
        
        try:
            teacher_idx = occ_perm.index('teacher')
            artist_idx = occ_perm.index('artist')
        except ValueError:
            continue
        
        book_perm = [None] * 6
        book_perm[A] = 'fantasy'
        book_perm[C] = 'mystery'
        book_perm[teacher_idx] = 'biography'
        book_perm[artist_idx] = 'science fiction'
        
        remaining_book_positions = [i for i in range(6) if book_perm[i] is None]
        if len(remaining_book_positions) != 2:
            continue
        p1, p2 = remaining_book_positions
        
        valid = False
        if p1 < teacher_idx:
            book_perm[p1] = 'historical fiction'
            book_perm[p2] = 'romance'
            valid = True
        elif p2 < teacher_idx:
            book_perm[p1] = 'romance'
            book_perm[p2] = 'historical fiction'
            valid = True
        else:
            valid = False
        
        if not valid:
            continue
        
        rows = []
        for i in range(6):
            house_num = str(i + 1)
            rows.append([house_num, name_perm[i], book_perm[i], occ_perm[i]])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Occupation"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
        solution_found = True
        exit()

if not solution_found:
    print(json.dumps({"solution": {"header": [], "rows": []}}))