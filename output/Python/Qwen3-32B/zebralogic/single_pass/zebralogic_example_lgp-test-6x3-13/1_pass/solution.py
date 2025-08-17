import itertools
import json

names_list = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
other_names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter']

occupations_list = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']
other_occupations = ['artist', 'nurse', 'engineer', 'teacher', 'lawyer']

book_genres_list = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']

for names_perm in itertools.permutations(other_names):
    # Construct names with Eric in position 2 (third house)
    names = [names_perm[0], names_perm[1], 'Eric', names_perm[2], names_perm[3], names_perm[4]]
    
    for occupations_perm in itertools.permutations(other_occupations):
        occupations = ['doctor'] + list(occupations_perm)
        
        for book_genres_perm in itertools.permutations(book_genres_list):
            # Check if Alice's book genre is fantasy
            try:
                alice_pos = names.index('Alice')
            except ValueError:
                continue
            
            if book_genres_perm[alice_pos] != 'fantasy':
                continue
            
            # Check if Alice's occupation is lawyer (clue 4)
            if occupations[alice_pos] != 'lawyer':
                continue
            
            # Check per-house constraints
            valid = True
            for i in range(6):
                # Check if teacher's book is biography
                if occupations[i] == 'teacher' and book_genres_perm[i] != 'biography':
                    valid = False
                    break
                # Check if artist's book is science fiction
                if occupations[i] == 'artist' and book_genres_perm[i] != 'science fiction':
                    valid = False
                    break
                # Check if Carol's book is mystery
                if names[i] == 'Carol' and book_genres_perm[i] != 'mystery':
                    valid = False
                    break
            if not valid:
                continue
            
            # Check clue 5: Bob not in fifth house (index 4)
            try:
                bob_pos = names.index('Bob')
            except ValueError:
                continue
            if bob_pos == 4:
                continue
            
            # Check clue 2: Carol and Bob are adjacent
            try:
                carol_pos = names.index('Carol')
            except ValueError:
                continue
            if abs(carol_pos - bob_pos) != 1:
                continue
            
            # Check clue 13: Carol (mystery) not in fifth house
            if carol_pos == 4:
                continue
            
            # Check clue 7: nurse is directly left of Alice
            try:
                nurse_pos = occupations.index('nurse')
            except ValueError:
                continue
            if nurse_pos + 1 != alice_pos:
                continue
            
            # Check clue 6: Arnold left of engineer
            try:
                arnold_pos = names.index('Arnold')
            except ValueError:
                continue
            try:
                engineer_pos = occupations.index('engineer')
            except ValueError:
                continue
            if arnold_pos >= engineer_pos:
                continue
            
            # Check clue 9: historical fiction left of teacher
            try:
                teacher_pos = occupations.index('teacher')
            except ValueError:
                continue
            h_f_pos = -1
            for i in range(6):
                if book_genres_perm[i] == 'historical fiction':
                    h_f_pos = i
                    break
            if h_f_pos == -1:
                continue
            if h_f_pos >= teacher_pos:
                continue
            
            # All constraints satisfied, build solution
            solution_rows = []
            for house_num in range(6):
                house = str(house_num + 1)
                name = names[house_num]
                book = book_genres_perm[house_num]
                occupation = occupations[house_num]
                solution_rows.append([house, name, book, occupation])
            
            solution = {
                "solution": {
                    "header": ["House", "Name", "BookGenre", "Occupation"],
                    "rows": solution_rows
                }
            }
            
            print(json.dumps(solution))
            exit()