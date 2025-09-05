import itertools
import json

def main():
    names = ['Arnold', 'Eric', 'Peter']
    music_genres = ['pop', 'rock', 'classical']
    children = ['Fred', 'Meredith', 'Bella']
    book_genres = ['mystery', 'romance', 'science fiction']
    
    for name_perm in itertools.permutations(names):
        if name_perm[0] != 'Peter':
            continue
            
        for music_perm in itertools.permutations(music_genres):
            for child_perm in itertools.permutations(children):
                for book_perm in itertools.permutations(book_genres):
                    assignment = {
                        'name': name_perm,
                        'music': music_perm,
                        'child': child_perm,
                        'book': book_perm
                    }
                    
                    # Find index of mystery books
                    mystery_index = None
                    for i, book in enumerate(book_perm):
                        if book == 'mystery':
                            mystery_index = i
                            break
                    if mystery_index is None:
                        continue
                    
                    # Clue 5: Eric loves mystery books
                    if name_perm[mystery_index] != 'Eric':
                        continue
                    
                    # Clue 3: Mystery books lover loves classical music
                    if music_perm[mystery_index] != 'classical':
                        continue
                    
                    # Clue 1: Fred's child left of mystery books
                    fred_index = None
                    for i, ch in enumerate(child_perm):
                        if ch == 'Fred':
                            fred_index = i
                            break
                    if fred_index is None or fred_index != mystery_index - 1:
                        continue
                    
                    # Clue 4: Sci-fi book lover has Meredith child
                    scifi_index = None
                    for i, book in enumerate(book_perm):
                        if book == 'science fiction':
                            scifi_index = i
                            break
                    if scifi_index is None or child_perm[scifi_index] != 'Meredith':
                        continue
                    
                    # Clue 6: Rock music right of romance books
                    romance_index = None
                    for i, book in enumerate(book_perm):
                        if book == 'romance':
                            romance_index = i
                            break
                    rock_index = None
                    for i, music in enumerate(music_perm):
                        if music == 'rock':
                            rock_index = i
                            break
                    if romance_index is None or rock_index is None or rock_index <= romance_index:
                        continue
                    
                    # Build solution
                    rows = []
                    for i in range(3):
                        rows.append([
                            str(i+1),
                            name_perm[i],
                            music_perm[i],
                            child_perm[i],
                            book_perm[i]
                        ])
                    
                    result = {
                        "solution": {
                            "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                            "rows": rows
                        }
                    }
                    print(json.dumps(result))
                    return
                    
    print('{"solution": {"header": ["House", "Name", "MusicGenre", "Children", "BookGenre"], "rows": []}}')

if __name__ == '__main__':
    main()