import itertools
import json

def main():
    names = ['Eric', 'Arnold', 'Peter']
    smoothies = ['desert', 'watermelon', 'cherry']
    books = ['science fiction', 'romance', 'mystery']
    
    remaining_names = ['Eric', 'Arnold']
    solution_found = False
    result_dict = None
    
    for name_perm in itertools.permutations(remaining_names):
        assignment_names = ['Peter', name_perm[0], name_perm[1]]
        
        for smoothie_perm in itertools.permutations(smoothies):
            assignment_smoothies = list(smoothie_perm)
            
            for book_perm in itertools.permutations(books):
                assignment_books = list(book_perm)
                
                arnold_index = assignment_names.index('Arnold')
                if assignment_books[arnold_index] != 'mystery':
                    continue
                
                if assignment_books[0] == 'science fiction':
                    continue
                
                if arnold_index < 1:
                    continue
                if assignment_smoothies[arnold_index-1] != 'desert':
                    continue
                
                if 'cherry' not in assignment_smoothies:
                    continue
                cherry_index = assignment_smoothies.index('cherry')
                if cherry_index >= arnold_index:
                    continue
                
                rows = []
                for i in range(3):
                    house_number = str(i + 1)
                    row = [house_number, assignment_names[i], assignment_smoothies[i], assignment_books[i]]
                    rows.append(row)
                
                result_dict = {
                    "solution": {
                        "header": ["House", "Name", "Smoothie", "Book"],
                        "rows": rows
                    }
                }
                solution_found = True
                break
            
            if solution_found:
                break
        if solution_found:
            break
    
    if solution_found:
        print(json.dumps(result_dict, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()