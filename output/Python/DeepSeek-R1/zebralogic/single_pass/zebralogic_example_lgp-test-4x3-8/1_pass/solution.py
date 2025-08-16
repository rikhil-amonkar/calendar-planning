import itertools
import json

def main():
    names = ("Eric", "Arnold", "Peter", "Alice")
    hair_colors = ("blonde", "black", "brown", "red")
    music_genres = ("pop", "jazz", "rock", "classical")
    
    music_perms = list(itertools.permutations(music_genres))
    music_perms = [p for p in music_perms if p[0] == 'classical']
    
    hair_perms = list(itertools.permutations(hair_colors))
    hair_perms = [p for p in hair_perms if p[1] == 'blonde']
    
    found = False
    solution_data = None
    
    for n_perm in itertools.permutations(names):
        if found:
            break
        for h_perm in hair_perms:
            if found:
                break
            for m_perm in music_perms:
                if h_perm[0] == 'brown':
                    continue
                if m_perm[2] == 'pop':
                    continue
                
                try:
                    i_eric = n_perm.index('Eric')
                except ValueError:
                    continue
                if h_perm[i_eric] != 'red':
                    continue
                
                try:
                    i_jazz = m_perm.index('jazz')
                except ValueError:
                    continue
                try:
                    i_red = h_perm.index('red')
                except ValueError:
                    continue
                if i_jazz != i_red:
                    continue
                
                try:
                    i_rock = m_perm.index('rock')
                except ValueError:
                    continue
                if n_perm[i_rock] != 'Arnold':
                    continue
                
                try:
                    i_peter = n_perm.index('Peter')
                except ValueError:
                    continue
                if i_peter <= i_rock:
                    continue
                
                rows = []
                for i in range(4):
                    rows.append([str(i+1), n_perm[i], h_perm[i], m_perm[i]])
                
                solution_data = {
                    "solution": {
                        "header": ["House", "Name", "HairColor", "MusicGenre"],
                        "rows": rows
                    }
                }
                found = True
                break
    
    if solution_data is None:
        solution_data = {"error": "No solution found"}
    
    print(json.dumps(solution_data))

if __name__ == '__main__':
    main()