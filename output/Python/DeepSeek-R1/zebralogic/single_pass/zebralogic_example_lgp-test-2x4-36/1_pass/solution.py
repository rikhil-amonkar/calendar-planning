import json
from itertools import permutations

def main():
    names = ['Eric', 'Arnold']
    genres = ['science fiction', 'mystery']
    months = ['april', 'sept']
    animals = ['horse', 'cat']
    
    found = False
    solution_dict = None
    
    for name_perm in permutations(names):
        for genre_perm in permutations(genres):
            for month_perm in permutations(months):
                for animal_perm in permutations(animals):
                    n1, n2 = name_perm
                    g1, g2 = genre_perm
                    m1, m2 = month_perm
                    a1, a2 = animal_perm
                    
                    if n1 == 'Eric' and m1 == 'sept' and g2 == 'science fiction' and a1 == 'horse':
                        row1 = ['1', n1, g1, m1, a1]
                        row2 = ['2', n2, g2, m2, a2]
                        header = ["House", "Name", "Favorite Book Genre", "Birthday Month", "Animal"]
                        solution_dict = {
                            "solution": {
                                "header": header,
                                "rows": [row1, row2]
                            }
                        }
                        found = True
                        break
                if found:
                    break
            if found:
                break
        if found:
            break
    
    if found:
        print(json.dumps(solution_dict))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()