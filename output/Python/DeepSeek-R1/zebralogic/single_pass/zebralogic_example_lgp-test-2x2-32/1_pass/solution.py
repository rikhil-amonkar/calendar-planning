import itertools
import json

def main():
    names = ['Eric', 'Arnold']
    book_genres = ['science fiction', 'mystery']
    
    attr_name = "name"
    attr_book = "favorite book genres"
    
    found = False
    result_data = None
    
    for name_perm in itertools.permutations(names):
        if found:
            break
        for book_perm in itertools.permutations(book_genres):
            house1 = {attr_name: name_perm[0], attr_book: book_perm[0]}
            house2 = {attr_name: name_perm[1], attr_book: book_perm[1]}
            
            if house1[attr_name] == 'Eric' and house2[attr_book] == 'mystery':
                header = ["House", attr_name, attr_book]
                row1 = ["1", house1[attr_name], house1[attr_book]]
                row2 = ["2", house2[attr_name], house2[attr_book]]
                result_data = {
                    "solution": {
                        "header": header,
                        "rows": [row1, row2]
                    }
                }
                found = True
                break
    
    if not found:
        result_data = {"solution": {}}
    
    print(json.dumps(result_data))

if __name__ == "__main__":
    main()