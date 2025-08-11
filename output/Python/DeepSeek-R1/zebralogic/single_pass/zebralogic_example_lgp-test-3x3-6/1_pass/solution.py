import json
from itertools import permutations

def main():
    names = ['Eric', 'Arnold', 'Peter']
    books = ['mystery', 'science fiction', 'romance']
    vacations = ['mountain', 'beach', 'city']
    
    found_solution = None
    
    for name_perm in permutations(names):
        for book_perm in permutations(books):
            for vacation_perm in permutations(vacations):
                name_to_house = {}
                for idx, name in enumerate(name_perm):
                    house = idx + 1
                    name_to_house[name] = house
                
                if name_to_house['Eric'] + 1 != name_to_house['Arnold']:
                    continue
                
                peter_house = name_to_house['Peter']
                if vacation_perm[peter_house - 1] != 'city':
                    continue
                
                beach_house = None
                for i, vac in enumerate(vacation_perm):
                    if vac == 'beach':
                        beach_house = i + 1
                        break
                if beach_house is None:
                    continue
                
                if peter_house <= beach_house:
                    continue
                
                mystery_house = None
                scifi_house = None
                for i, book in enumerate(book_perm):
                    if book == 'mystery':
                        mystery_house = i + 1
                    elif book == 'science fiction':
                        scifi_house = i + 1
                if mystery_house is None or scifi_house is None:
                    continue
                
                if mystery_house >= beach_house:
                    continue
                
                if scifi_house != beach_house:
                    continue
                
                rows = []
                for i in range(3):
                    row = [str(i+1), name_perm[i], book_perm[i], vacation_perm[i]]
                    rows.append(row)
                found_solution = rows
                break
            if found_solution is not None:
                break
        if found_solution is not None:
            break
    
    if found_solution is None:
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Book Genre", "Vacation Type"],
                "rows": []
            }
        }
    else:
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Book Genre", "Vacation Type"],
                "rows": found_solution
            }
        }
    
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()