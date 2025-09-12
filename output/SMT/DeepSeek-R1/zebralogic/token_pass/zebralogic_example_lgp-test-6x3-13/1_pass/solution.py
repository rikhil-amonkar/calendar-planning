import json
from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # House indices
    houses = [1, 2, 3, 4, 5, 6]
    
    # Attributes
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    books = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']
    
    # Create variables for each attribute's house assignment
    name_vars = {name: Int(f'n_{name}') for name in names}
    book_vars = {book: Int(f'b_{book}') for book in books}
    occ_vars = {occ: Int(f'o_{occ}') for occ in occupations}
    
    # Constrain all attributes to be between 1 and 6
    for var in list(name_vars.values()) + list(book_vars.values()) + list(occ_vars.values()):
        s.add(var >= 1, var <= 6)
    
    # Each attribute type must have distinct house assignments
    s.add(Distinct(list(name_vars.values())))
    s.add(Distinct(list(book_vars.values())))
    s.add(Distinct(list(occ_vars.values())))
    
    # Add clues
    # 1. Alice is the person who loves fantasy books.
    s.add(name_vars['Alice'] == book_vars['fantasy'])
    
    # 2. The person who loves mystery books and Bob are next to each other.
    # 3. Carol is the person who loves mystery books.
    # So Carol and Bob are adjacent
    s.add(Abs(name_vars['Carol'] - name_vars['Bob']) == 1)
    
    # 4. The person who is a lawyer is the person who loves fantasy books.
    s.add(occ_vars['lawyer'] == book_vars['fantasy'])
    
    # 5. Bob is not in the fifth house.
    s.add(name_vars['Bob'] != 5)
    
    # 6. Arnold is somewhere to the left of the person who is an engineer.
    s.add(name_vars['Arnold'] < occ_vars['engineer'])
    
    # 7. The person who is a nurse is directly left of Alice.
    s.add(occ_vars['nurse'] == name_vars['Alice'] - 1)
    
    # 8. The person who loves biography books is the person who is a teacher.
    s.add(book_vars['biography'] == occ_vars['teacher'])
    
    # 9. The person who loves historical fiction books is somewhere to the left of the person who is a teacher.
    s.add(book_vars['historical fiction'] < occ_vars['teacher'])
    
    # 10. The person who is a doctor is in the first house.
    s.add(occ_vars['doctor'] == 1)
    
    # 11. The person who loves science fiction books is the person who is an artist.
    s.add(book_vars['science fiction'] == occ_vars['artist'])
    
    # 12. Eric is in the third house.
    s.add(name_vars['Eric'] == 3)
    
    # 13. The person who loves mystery books is not in the fifth house.
    s.add(book_vars['mystery'] != 5)
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        
        # Create solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Occupation"],
                "rows": []
            }
        }
        
        # For each house, find the assigned attributes
        for house in houses:
            # Find name
            name = next(n for n in names if m.eval(name_vars[n]).as_long() == house)
            # Find book genre
            book = next(b for b in books if m.eval(book_vars[b]).as_long() == house)
            # Find occupation
            occupation = next(o for o in occupations if m.eval(occ_vars[o]).as_long() == house)
            
            solution["solution"]["rows"].append([str(house), name, book, occupation])
        
        # Output JSON
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()