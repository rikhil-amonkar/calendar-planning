import json

def main():
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    books = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']
    
    num_houses = 6
    names_domains = [set(names) for _ in range(num_houses)]
    books_domains = [set(books) for _ in range(num_houses)]
    occupations_domains = [set(occupations) for _ in range(num_houses)]
    
    # Apply fixed constraints
    occupations_domains[0] = {'doctor'}
    names_domains[2] = {'Eric'}
    if 'Bob' in names_domains[4]:
        names_domains[4].remove('Bob')
    if 'mystery' in books_domains[4]:
        books_domains[4].remove('mystery')
    
    for i in range(1, num_houses):
        if 'doctor' in occupations_domains[i]:
            occupations_domains[i].remove('doctor')
    for i in range(num_houses):
        if i != 2 and 'Eric' in names_domains[i]:
            names_domains[i].remove('Eric')
    
    for i in range(num_houses):
        if 'Alice' in names_domains[i]:
            books_domains[i] = books_domains[i] & {'fantasy'}
            occupations_domains[i] = occupations_domains[i] & {'lawyer'}
        if 'fantasy' in books_domains[i]:
            names_domains[i] = names_domains[i] & {'Alice'}
            occupations_domains[i] = occupations_domains[i] & {'lawyer'}
        if 'lawyer' in occupations_domains[i]:
            names_domains[i] = names_domains[i] & {'Alice'}
            books_domains[i] = books_domains[i] & {'fantasy'}
        
        if 'Carol' in names_domains[i]:
            books_domains[i] = books_domains[i] & {'mystery'}
        if 'mystery' in books_domains[i]:
            names_domains[i] = names_domains[i] & {'Carol'}
        
        if 'biography' in books_domains[i]:
            occupations_domains[i] = occupations_domains[i] & {'teacher'}
        if 'teacher' in occupations_domains[i]:
            books_domains[i] = books_domains[i] & {'biography'}
        
        if 'science fiction' in books_domains[i]:
            occupations_domains[i] = occupations_domains[i] & {'artist'}
        if 'artist' in occupations_domains[i]:
            books_domains[i] = books_domains[i] & {'science fiction'}
    
    if 'nurse' in occupations_domains[5]:
        occupations_domains[5].remove('nurse')
    
    for i in [0, 1]:
        if 'Alice' in names_domains[i]:
            names_domains[i].remove('Alice')
    for i in range(2, 6):
        if 'Alice' in names_domains[i]:
            if 'nurse' not in occupations_domains[i-1]:
                names_domains[i].discard('Alice')
    for i in range(1, 5):
        if 'nurse' in occupations_domains[i]:
            if 'Alice' not in names_domains[i+1]:
                occupations_domains[i].discard('nurse')
    
    assignment = [None] * num_houses
    used_names = set()
    used_books = set()
    used_occupations = set()
    
    def is_consistent(assignment, i):
        current = assignment[i]
        if current['name'] == 'Alice':
            if current['book'] != 'fantasy' or current['occupation'] != 'lawyer':
                return False
        if current['name'] == 'Carol':
            if current['book'] != 'mystery':
                return False
        if current['book'] == 'mystery':
            if current['name'] != 'Carol':
                return False
        if current['book'] == 'biography':
            if current['occupation'] != 'teacher':
                return False
        if current['occupation'] == 'teacher':
            if current['book'] != 'biography':
                return False
        if current['book'] == 'science fiction':
            if current['occupation'] != 'artist':
                return False
        if current['occupation'] == 'artist':
            if current['book'] != 'science fiction':
                return False
        if current['book'] == 'fantasy':
            if current['name'] != 'Alice' or current['occupation'] != 'lawyer':
                return False
        if current['occupation'] == 'lawyer':
            if current['book'] != 'fantasy' or current['name'] != 'Alice':
                return False
        
        if i == 4:
            if current['name'] == 'Bob':
                return False
            if current['book'] == 'mystery':
                return False
        if i == 2:
            if current['name'] != 'Eric':
                return False
        
        bob_house = None
        mystery_house = None
        for j in range(i+1):
            if assignment[j]['name'] == 'Bob':
                bob_house = j
            if assignment[j]['book'] == 'mystery':
                mystery_house = j
        if bob_house is not None and mystery_house is not None:
            if abs(bob_house - mystery_house) != 1:
                return False
        
        arnold_house = None
        engineer_house = None
        for j in range(i+1):
            if assignment[j]['name'] == 'Arnold':
                arnold_house = j
            if assignment[j]['occupation'] == 'engineer':
                engineer_house = j
        if arnold_house is not None and engineer_house is not None:
            if arnold_house >= engineer_house:
                return False
        
        hist_house = None
        teacher_house = None
        for j in range(i+1):
            if assignment[j]['book'] == 'historical fiction':
                hist_house = j
            if assignment[j]['occupation'] == 'teacher':
                teacher_house = j
        if hist_house is not None and teacher_house is not None:
            if hist_house >= teacher_house:
                return False
        
        for j in range(i):
            if assignment[j]['occupation'] == 'nurse':
                if assignment[j+1]['name'] != 'Alice':
                    return False
        
        if current['occupation'] == 'nurse' and i == 5:
            return False
        
        if i == 0:
            if current['occupation'] != 'doctor':
                return False
        else:
            if 0 <= i and assignment[0]['occupation'] != 'doctor':
                return False
        
        return True
    
    def backtrack(i, used_names, used_books, used_occupations, assignment):
        if i == num_houses:
            return assignment
        
        available_names = names_domains[i] - used_names
        available_books = books_domains[i] - used_books
        available_occupations = occupations_domains[i] - used_occupations
        
        for name in available_names:
            for book in available_books:
                for occupation in available_occupations:
                    assignment[i] = {'name': name, 'book': book, 'occupation': occupation}
                    if is_consistent(assignment, i):
                        used_names.add(name)
                        used_books.add(book)
                        used_occupations.add(occupation)
                        result = backtrack(i+1, used_names, used_books, used_occupations, assignment)
                        if result is not None:
                            return result
                        used_names.remove(name)
                        used_books.remove(book)
                        used_occupations.remove(occupation)
                    assignment[i] = None
        return None
    
    sol = backtrack(0, used_names, used_books, used_occupations, assignment)
    if sol is None:
        print("No solution found")
        return
    
    rows = []
    for idx, house in enumerate(sol):
        house_number = str(idx+1)
        name = house['name']
        book = house['book']
        occupation = house['occupation']
        rows.append([house_number, name, book, occupation])
    
    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()