import itertools
import json

def solve_puzzle():
    names = ['Arnold', 'Eric', 'Peter', 'Alice', 'Carol', 'Bob']
    music_genres = ['jazz', 'pop', 'classical', 'rock', 'hip hop', 'country']
    
    # Generate name permutations where Carol is in house 6 (index 5)
    name_candidates = []
    other_names = ['Arnold', 'Eric', 'Peter', 'Alice', 'Bob']
    for p in itertools.permutations(other_names):
        name_candidate = list(p) + ['Carol']
        name_candidates.append(name_candidate)
    
    # Generate music permutations where house 3 (index 2) is hip hop, house 6 (index 5) is country
    music_candidates = []
    for p in itertools.permutations(music_genres):
        if p[2] == 'hip hop' and p[5] == 'country':
            music_candidates.append(p)
    
    # Check each combination
    for name_perm in name_candidates:
        for music_perm in music_candidates:
            # Check clue 8: Peter's music is pop
            peter_pos = name_perm.index('Peter')
            if music_perm[peter_pos] != 'pop':
                continue
            
            # Check clue 10: one house between Peter and Bob
            bob_pos = name_perm.index('Bob')
            if abs(peter_pos - bob_pos) != 2:
                continue
            
            # Check clue 1: Bob is directly left of jazz
            if bob_pos + 1 >= 6 or music_perm[bob_pos + 1] != 'jazz':
                continue
            
            # Check clue 2: Eric is left of hip-hop (house 3, index 2)
            eric_pos = name_perm.index('Eric')
            if eric_pos >= 2:
                continue
            
            # Check clue 4: Eric and hip-hop (index 2) are adjacent. So eric_pos must be 1 (since 2-1=1)
            if eric_pos != 1:
                continue
            
            # Check clue 6: Arnold not in fifth house (index 4)
            arnold_pos = name_perm.index('Arnold')
            if arnold_pos == 4:
                continue
            
            # Check clue 7: Arnold is right of Peter
            if arnold_pos <= peter_pos:
                continue
            
            # Check clue 11: rock not in fifth house (index 4)
            if music_perm[4] == 'rock':
                continue
            
            # All constraints passed, build solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "MusicGenre"],
                    "rows": []
                }
            }
            for i in range(6):
                house_num = str(i + 1)
                name = name_perm[i]
                music = music_perm[i]
                solution["solution"]["rows"].append([house_num, name, music])
            
            print(json.dumps(solution))
            return
    
    # If no solution found
    print(json.dumps({"solution": {"header": [], "rows": []}}))

solve_puzzle()