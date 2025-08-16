import z3
import json

def main():
    # Define enums for Name and BookGenre
    NameSort, name_consts = z3.EnumSort('Name', ['Eric', 'Arnold'])
    Eric, Arnold = name_consts
    GenreSort, genre_consts = z3.EnumSort('BookGenre', ['science fiction', 'mystery'])
    science_fiction, mystery = genre_consts

    # Create variables for house attributes
    house1_name = z3.Const('house1_name', NameSort)
    house1_genre = z3.Const('house1_genre', GenreSort)
    house2_name = z3.Const('house2_name', NameSort)
    house2_genre = z3.Const('house2_genre', GenreSort)

    s = z3.Solver()

    # All names are distinct
    s.add(z3.Distinct(house1_name, house2_name))
    # All book genres are distinct
    s.add(z3.Distinct(house1_genre, house2_genre))

    # Clue 1: Eric is directly left of the person who loves mystery books.
    s.add(house1_name == Eric)
    s.add(house2_genre == mystery)

    if s.check() == z3.sat:
        m = s.model()
        # Helper function to get the string name of a constant
        def get_name(const):
            return const.decl().name()
        
        # Get values for house1
        h1_name = m[house1_name]
        h1_genre = m[house1_genre]
        h1_name_str = get_name(h1_name)
        h1_genre_str = get_name(h1_genre)
        
        # Get values for house2
        h2_name = m[house2_name]
        h2_genre = m[house2_genre]
        h2_name_str = get_name(h2_name)
        h2_genre_str = get_name(h2_genre)
        
        # Build the solution dictionary
        solution = {
            "header": ["House", "Name", "BookGenre"],
            "rows": [
                ["1", h1_name_str, h1_genre_str],
                ["2", h2_name_str, h2_genre_str]
            ]
        }
        
        # Output as JSON
        result = {"solution": solution}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()