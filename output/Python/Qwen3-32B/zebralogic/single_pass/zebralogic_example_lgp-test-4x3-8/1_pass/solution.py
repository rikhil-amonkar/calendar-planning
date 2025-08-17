import itertools
import json

def main():
    names = ['Eric', 'Arnold', 'Peter', 'Alice']
    hair_colors = ['blonde', 'black', 'brown', 'red']
    music_genres = ['pop', 'jazz', 'rock', 'classical']
    
    for name_perm in itertools.permutations(names):
        for hair_perm in itertools.permutations(hair_colors):
            for music_perm in itertools.permutations(music_genres):
                # Check clue 5: classical in first house
                if music_perm[0] != 'classical':
                    continue
                # Check clue 2: classical directly left of blonde (house 2 has blonde)
                if hair_perm[1] != 'blonde':
                    continue
                # Check clue 3: first house not brown
                if hair_perm[0] == 'brown':
                    continue
                # Check clue 4: pop not in third house
                if music_perm[2] == 'pop':
                    continue
                # Check clue 1: Eric has red hair
                eric_pos = None
                for i in range(4):
                    if name_perm[i] == 'Eric':
                        eric_pos = i
                        break
                if hair_perm[eric_pos] != 'red':
                    continue
                # Check clue 6: jazz is loved by red-haired (Eric)
                try:
                    jazz_pos = music_perm.index('jazz')
                except ValueError:
                    continue
                if hair_perm[jazz_pos] != 'red':
                    continue
                # Check clue 7: rock is Arnold's
                try:
                    rock_pos = music_perm.index('rock')
                except ValueError:
                    continue
                if name_perm[rock_pos] != 'Arnold':
                    continue
                # Check clue 8: Peter is to the right of rock
                peter_pos = name_perm.index('Peter')
                if peter_pos <= rock_pos:
                    continue
                
                # Build solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "HairColor", "MusicGenre"],
                        "rows": []
                    }
                }
                for i in range(4):
                    house_num = i + 1
                    row = [
                        str(house_num),
                        name_perm[i],
                        hair_perm[i],
                        music_perm[i]
                    ]
                    solution['solution']['rows'].append(row)
                
                # Output as JSON
                print(json.dumps(solution))
                return

main()