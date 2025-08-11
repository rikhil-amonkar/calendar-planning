import itertools
import json

def main():
    names = ['Peter', 'Arnold', 'Eric']
    books = ['science fiction', 'mystery', 'romance']
    smoothies = ['watermelon', 'desert', 'cherry']
    birthdays = ['april', 'jan', 'sept']
    heights = ['average', 'very short', 'short']
    
    name_perms = []
    for perm in itertools.permutations(names):
        if perm[0] == 'Eric':
            name_perms.append(perm)
            
    smoothie_perms = []
    for perm in itertools.permutations(smoothies):
        if perm[0] == 'watermelon':
            smoothie_perms.append(perm)
            
    height_perms = []
    for perm in itertools.permutations(heights):
        if perm[0] == 'short':
            height_perms.append(perm)
            
    book_perms = list(itertools.permutations(books))
    birthday_perms = list(itertools.permutations(birthdays))
    
    def check_candidate(candidate):
        if candidate[1][2] == 'cherry':
            return False
            
        for house in candidate:
            if house[0] == 'Arnold':
                if house[1] != 'mystery':
                    return False
            if house[1] == 'mystery':
                if house[0] != 'Arnold':
                    return False
                    
        if candidate[0][3] == 'jan':
            return False
            
        for house in candidate:
            if house[4] == 'very short':
                if house[1] != 'romance':
                    return False
                    
        for house in candidate:
            if house[1] == 'mystery':
                if house[3] != 'sept':
                    return False
                    
        for house in candidate:
            if house[4] == 'average':
                if house[2] != 'desert':
                    return False
                    
        return True
        
    solution_found = None
    for name_perm in name_perms:
        for book_perm in book_perms:
            for smoothie_perm in smoothie_perms:
                for birthday_perm in birthday_perms:
                    for height_perm in height_perms:
                        candidate = [
                            (name_perm[0], book_perm[0], smoothie_perm[0], birthday_perm[0], height_perm[0]),
                            (name_perm[1], book_perm[1], smoothie_perm[1], birthday_perm[1], height_perm[1]),
                            (name_perm[2], book_perm[2], smoothie_perm[2], birthday_perm[2], height_perm[2])
                        ]
                        if check_candidate(candidate):
                            solution_found = candidate
                            break
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
            
    if solution_found:
        header = ["House", "Name", "BookGenre", "Smoothie", "BirthdayMonth", "Height"]
        rows = []
        for i in range(3):
            row = [str(i+1)]
            row.append(solution_found[i][0])
            row.append(solution_found[i][1])
            row.append(solution_found[i][2])
            row.append(solution_found[i][3])
            row.append(solution_found[i][4])
            rows.append(row)
            
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": {}}))

if __name__ == "__main__":
    main()