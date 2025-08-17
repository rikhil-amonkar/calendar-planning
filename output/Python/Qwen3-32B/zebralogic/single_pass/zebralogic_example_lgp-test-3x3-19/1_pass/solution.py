import itertools
import json

def solve_puzzle():
    # Possible name permutations (Peter is first)
    names_options = [
        ['Peter', 'Arnold', 'Eric'],
        ['Peter', 'Eric', 'Arnold']
    ]
    
    # Generate all permutations for smoothies and books
    smoothie_perms = list(itertools.permutations(['desert', 'watermelon', 'cherry']))
    book_perms = list(itertools.permutations(['science fiction', 'romance', 'mystery']))
    
    for names in names_options:
        for smoothies in smoothie_perms:
            for books in book_perms:
                # Check constraint 2: Arnold's book is mystery
                arnold_index = names.index('Arnold')
                if books[arnold_index] != 'mystery':
                    continue
                
                # Check constraint 4: Desert is directly left of mystery
                try:
                    desert_index = smoothies.index('desert')
                except ValueError:
                    continue  # Should not happen with permutations
                mystery_index = books.index('mystery')
                if desert_index + 1 != mystery_index:
                    continue
                
                # Check constraint 1: Cherry is left of mystery
                try:
                    cherry_index = smoothies.index('cherry')
                except ValueError:
                    continue  # Should not happen with permutations
                if cherry_index >= mystery_index:
                    continue
                
                # Check constraint 3: Science fiction not in first house
                if books[0] == 'science fiction':
                    continue
                
                # Build the solution
                solution_data = {
                    "solution": {
                        "header": ["House", "Name", "Smoothie", "BookGenre"],
                        "rows": []
                    }
                }
                for i in range(3):
                    house_num = str(i + 1)
                    name = names[i]
                    smoothie = smoothies[i]
                    book = books[i]
                    solution_data['solution']['rows'].append([house_num, name, smoothie, book])
                
                # Return the first valid solution as JSON
                return json.dumps(solution_data)
    
    # If no solution found (should not happen)
    return None

# Run the solver and print the JSON result
result = solve_puzzle()
print(result)