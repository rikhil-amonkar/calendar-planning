import itertools
import json

def main():
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    hobbies = ['cooking', 'painting', 'gardening', 'photography']
    animals = ['horse', 'fish', 'cat', 'bird']
    book_genres = ['fantasy', 'mystery', 'romance', 'science fiction']
    birthday_months = ['april', 'jan', 'sept', 'feb']
    music_genres = ['pop', 'rock', 'classical', 'jazz']
    
    found = None
    
    for n in itertools.permutations(names):
        if n[1] == 'Eric':
            continue
            
        for h in itertools.permutations(hobbies):
            if h[2] == 'cooking':
                continue
                
            for a in itertools.permutations(animals):
                for b in itertools.permutations(book_genres):
                    if b[3] == 'romance':
                        continue
                    
                    cooking_index = h.index('cooking')
                    romance_index = b.index('romance')
                    if cooking_index != romance_index:
                        continue
                    
                    if romance_index == 0:
                        continue
                    if h[romance_index-1] != 'painting':
                        continue
                    
                    for bd in itertools.permutations(birthday_months):
                        feb_index = bd.index('feb')
                        fish_index = a.index('fish')
                        if feb_index != fish_index:
                            continue
                            
                        gardening_index = h.index('gardening')
                        april_index = bd.index('april')
                        if gardening_index != april_index:
                            continue
                            
                        for m in itertools.permutations(music_genres):
                            feb_index = bd.index('feb')
                            pop_index = m.index('pop')
                            if feb_index != pop_index:
                                continue
                            
                            horse_index = a.index('horse')
                            rock_index = m.index('rock')
                            if horse_index != rock_index:
                                continue
                            
                            jazz_index = m.index('jazz')
                            if jazz_index != cooking_index:
                                continue
                            
                            mystery_index = b.index('mystery')
                            if rock_index != mystery_index:
                                continue
                            
                            peter_index = n.index('Peter')
                            if peter_index != pop_index:
                                continue
                            
                            arnold_index = n.index('Arnold')
                            if gardening_index != arnold_index:
                                continue
                            
                            if rock_index == 3:
                                continue
                            if bd[rock_index+1] != 'jan':
                                continue
                            
                            fantasy_index = b.index('fantasy')
                            alice_index = n.index('Alice')
                            if alice_index <= fantasy_index:
                                continue
                            
                            cat_index = a.index('cat')
                            if cat_index <= horse_index:
                                continue
                            
                            found = (n, h, a, b, bd, m)
                            break
                        if found:
                            break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if found:
            break
            
    header = ["House", "Name", "Hobby", "Animals", "Favorite Book Genres", "Birthday Month", "Favorite Music Genres"]
    rows = []
    if found:
        n, h, a, b, bd, m = found
        for i in range(4):
            rows.append([
                str(i+1),
                n[i],
                h[i],
                a[i],
                b[i],
                bd[i],
                m[i]
            ])
        solution_dict = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
    else:
        solution_dict = {
            "solution": {
                "header": header,
                "rows": []
            }
        }
        
    print(json.dumps(solution_dict))

if __name__ == '__main__':
    main()