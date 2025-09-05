from z3 import *
import json

def main():
    # Create the solver
    s = Solver()
    
    # Define the house numbers
    houses = [1, 2, 3]
    
    # Define variables for each attribute's house position
    Eric = Int('Eric')
    Arnold = Int('Arnold')
    Peter = Int('Peter')
    
    mystery = Int('mystery')
    sci_fi = Int('sci_fi')
    romance = Int('romance')
    
    mountain = Int('mountain')
    beach = Int('beach')
    city = Int('city')
    
    # All variables must be between 1 and 3
    s.add(Eric >= 1, Eric <= 3)
    s.add(Arnold >= 1, Arnold <= 3)
    s.add(Peter >= 1, Peter <= 3)
    s.add(mystery >= 1, mystery <= 3)
    s.add(sci_fi >= 1, sci_fi <= 3)
    s.add(romance >= 1, romance <= 3)
    s.add(mountain >= 1, mountain <= 3)
    s.add(beach >= 1, beach <= 3)
    s.add(city >= 1, city <= 3)
    
    # All attributes within each category are distinct
    s.add(Distinct(Eric, Arnold, Peter))
    s.add(Distinct(mystery, sci_fi, romance))
    s.add(Distinct(mountain, beach, city))
    
    # Clue 1: Eric is directly left of Arnold
    s.add(Eric == Arnold - 1)
    
    # Clue 2: Peter is somewhere to the right of the person who loves beach vacations
    s.add(Peter > beach)
    
    # Clue 3: Peter is the person who prefers city breaks
    s.add(Peter == city)
    
    # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations
    s.add(mystery < beach)
    
    # Clue 5: The person who loves science fiction books is the person who loves beach vacations
    s.add(sci_fi == beach)
    
    # Check if satisfiable
    if s.check() == sat:
        m = s.model()
        
        # Create mapping from house number to attributes
        result = {}
        for house in houses:
            result[house] = {
                'Name': None,
                'BookGenre': None,
                'Vacation': None
            }
        
        # Map names to houses
        name_vars = [Eric, Arnold, Peter]
        name_strs = ['Eric', 'Arnold', 'Peter']
        for var, name in zip(name_vars, name_strs):
            house_num = m[var].as_long()
            result[house_num]['Name'] = name
        
        # Map book genres to houses
        book_vars = [mystery, sci_fi, romance]
        book_strs = ['mystery', 'science fiction', 'romance']
        for var, genre in zip(book_vars, book_strs):
            house_num = m[var].as_long()
            result[house_num]['BookGenre'] = genre
        
        # Map vacation types to houses
        vacation_vars = [mountain, beach, city]
        vacation_strs = ['mountain', 'beach', 'city']
        for var, vacation_type in zip(vacation_vars, vacation_strs):
            house_num = m[var].as_long()
            result[house_num]['Vacation'] = vacation_type
        
        # Prepare JSON output
        rows = []
        for house in sorted(result.keys()):
            attr = result[house]
            rows.append([str(house), attr['Name'], attr['BookGenre'], attr['Vacation']])
        
        output = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation"],
                "rows": rows
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()