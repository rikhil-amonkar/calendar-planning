import json
from z3 import *

def main():
    # Define Enum sorts
    Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
    BookGenre, (SciFi, Mystery) = EnumSort('BookGenre', ['SciFi', 'Mystery'])

    # Create variables for each house
    name1 = Const('name1', Name)
    genre1 = Const('genre1', BookGenre)
    name2 = Const('name2', Name)
    genre2 = Const('genre2', BookGenre)

    solver = Solver()

    # Add constraints
    solver.add(name1 != name2)
    solver.add(genre1 != genre2)
    solver.add(Implies(name1 == Eric, genre2 == Mystery))
    solver.add(name2 != Eric)

    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()

        # Helper functions to extract values from the model
        def get_name(const):
            return model.eval(const).decl().name()

        def get_book_genre(const):
            bg = model.eval(const).decl().name()
            if bg == 'SciFi':
                return 'science fiction'
            elif bg == 'Mystery':
                return 'mystery'
            else:
                raise ValueError("Unknown BookGenre")

        # Extract values for each house
        house1_name = get_name(name1)
        house1_book = get_book_genre(genre1)
        house2_name = get_name(name2)
        house2_book = get_book_genre(genre2)

        # Build JSON structure
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre"],
                "rows": [
                    ["1", house1_name, house1_book],
                    ["2", house2_name, house2_book]
                ]
            }
        }

        # Print JSON
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()