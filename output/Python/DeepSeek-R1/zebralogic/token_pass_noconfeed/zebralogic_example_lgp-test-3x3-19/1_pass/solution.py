import itertools
import json

def main():
    names = ['Eric', 'Arnold', 'Peter']
    smoothies = ['desert', 'watermelon', 'cherry']
    books = ['science fiction', 'romance', 'mystery']
    
    for name_perm in itertools.permutations(names):
        for smoothie_perm in itertools.permutations(smoothies):
            for book_perm in itertools.permutations(books):
                assignment = [
                    (name_perm[0], smoothie_perm[0], book_perm[0]),
                    (name_perm[1], smoothie_perm[1], book_perm[1]),
                    (name_perm[2], smoothie_perm[2], book_perm[2])
                ]
                
                # Check constraints
                # Constraint 5: Peter in first house
                if assignment[0][0] != 'Peter':
                    continue
                    
                # Constraint 2: Arnold loves mystery books
                arnold_house = next(i for i, attr in enumerate(assignment) if attr[0] == 'Arnold')
                if assignment[arnold_house][2] != 'mystery':
                    continue
                    
                # Constraint 3: Science fiction not in first house
                if assignment[0][2] == 'science fiction':
                    continue
                    
                # Constraint 4: Desert smoothie directly left of mystery books
                mystery_house = next(i for i, attr in enumerate(assignment) if attr[2] == 'mystery')
                if mystery_house == 0:
                    continue  # Cannot have left neighbor
                if assignment[mystery_house-1][1] != 'desert':
                    continue
                    
                # Constraint 1: Cherry smoothie left of mystery books
                cherry_house = next(i for i, attr in enumerate(assignment) if attr[1] == 'cherry')
                if cherry_house >= mystery_house:
                    continue
                    
                # All constraints satisfied - build solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Smoothie", "BookGenre"],
                        "rows": [
                            ["1", assignment[0][0], assignment[0][1], assignment[0][2]],
                            ["2", assignment[1][0], assignment[1][1], assignment[1][2]],
                            ["3", assignment[2][0], assignment[2][1], assignment[2][2]]
                        ]
                    }
                }
                print(json.dumps(solution, indent=2))
                return
                
    print("No solution found")

if __name__ == "__main__":
    main()