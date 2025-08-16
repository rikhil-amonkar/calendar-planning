from z3 import *

def main():
    # Define enums for attributes
    Name, (Eric, Arnold, Peter) = EnumSort('Name', ['Eric', 'Arnold', 'Peter'])
    Book, (mystery, science_fiction, romance) = EnumSort('Book', ['mystery', 'science_fiction', 'romance'])
    Vacation, (mountain, beach, city) = EnumSort('Vacation', ['mountain', 'beach', 'city'])
    
    # Create variables for each house
    n1, n2, n3 = Consts('n1 n2 n3', Name)
    b1, b2, b3 = Consts('b1 b2 b3', Book)
    v1, v2, v3 = Consts('v1 v2 v3', Vacation)
    
    s = Solver()
    
    # All attributes are unique per house
    s.add(Distinct(n1, n2, n3))
    s.add(Distinct(b1, b2, b3))
    s.add(Distinct(v1, v2, v3))
    
    # Clue 1: Eric is directly left of Arnold
    s.add(Or(
        And(n1 == Eric, n2 == Arnold),
        And(n2 == Eric, n3 == Arnold)
    ))
    
    # Clue 2: Peter is right of the beach vacation lover
    s.add(Or(
        And(v1 == beach, Or(n2 == Peter, n3 == Peter)),
        And(v2 == beach, n3 == Peter)
    ))
    
    # Clue 3: Peter prefers city breaks
    s.add(Or(
        And(n1 == Peter, v1 == city),
        And(n2 == Peter, v2 == city),
        And(n3 == Peter, v3 == city)
    ))
    
    # Clue 4: Mystery book lover is left of beach vacation lover
    # Since beach vacation lover is the same as science fiction book lover (clue5), 
    # we express: mystery is left of science_fiction
    s.add(Or(
        And(b1 == mystery, b2 == science_fiction),
        And(b1 == mystery, b3 == science_fiction),
        And(b2 == mystery, b3 == science_fiction)
    ))
    
    # Clue 5: Science fiction book lover is the beach vacation lover
    s.add(And(
        (b1 == science_fiction) == (v1 == beach),
        (b2 == science_fiction) == (v2 == beach),
        (b3 == science_fiction) == (v3 == beach)
    ))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        
        # Function to map book genre string
        def map_book(book_str):
            if book_str == 'science_fiction':
                return 'science fiction'
            return book_str
        
        # Extract values for each house
        house1 = [
            str(m[n1]),
            map_book(str(m[b1])),
            str(m[v1])
        ]
        house2 = [
            str(m[n2]),
            map_book(str(m[b2])),
            str(m[v2])
        ]
        house3 = [
            str(m[n3]),
            map_book(str(m[b3])),
            str(m[v3])
        ]
        
        # Format the solution as JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation"],
                "rows": [
                    ["1"] + house1,
                    ["2"] + house2,
                    ["3"] + house3
                ]
            }
        }
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()