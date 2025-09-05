import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the attributes with integer mappings
    names = {"Arnold": 1, "Eric": 2, "Peter": 3}
    music_genres = {"pop": 1, "rock": 2, "classical": 3}
    children = {"Fred": 1, "Meredith": 2, "Bella": 3}
    book_genres = {"mystery": 1, "romance": 2, "science fiction": 3}
    
    # Create variables for each house attribute
    n1, n2, n3 = z3.Ints('n1 n2 n3')  # names for houses 1,2,3
    m1, m2, m3 = z3.Ints('m1 m2 m3')  # music genres
    c1, c2, c3 = z3.Ints('c1 c2 c3')  # children
    b1, b2, b3 = z3.Ints('b1 b2 b3')  # book genres
    
    # All attributes must be within their respective ranges
    solver.add(z3.And(n1 >= 1, n1 <= 3, n2 >= 1, n2 <= 3, n3 >= 1, n3 <= 3))
    solver.add(z3.And(m1 >= 1, m1 <= 3, m2 >= 1, m2 <= 3, m3 >= 1, m3 <= 3))
    solver.add(z3.And(c1 >= 1, c1 <= 3, c2 >= 1, c2 <= 3, c3 >= 1, c3 <= 3))
    solver.add(z3.And(b1 >= 1, b1 <= 3, b2 >= 1, b2 <= 3, b3 >= 1, b3 <= 3))
    
    # All attributes within a category must be distinct
    solver.add(z3.Distinct(n1, n2, n3))
    solver.add(z3.Distinct(m1, m2, m3))
    solver.add(z3.Distinct(c1, c2, c3))
    solver.add(z3.Distinct(b1, b2, b3))
    
    # Clue 2: Peter is in the first house
    solver.add(n1 == names["Peter"])
    
    # Clue 5: Eric is the person who loves mystery books
    # Clue 3: The person who loves mystery books loves classical music
    # So Eric loves classical music and mystery books
    mystery_house = z3.Int('mystery_house')
    solver.add(z3.Or(
        z3.And(b1 == book_genres["mystery"], mystery_house == 1),
        z3.And(b2 == book_genres["mystery"], mystery_house == 2),
        z3.And(b3 == book_genres["mystery"], mystery_house == 3)
    ))
    solver.add(z3.Or(
        z3.And(mystery_house == 1, n1 == names["Eric"], m1 == music_genres["classical"]),
        z3.And(mystery_house == 2, n2 == names["Eric"], m2 == music_genres["classical"]),
        z3.And(mystery_house == 3, n3 == names["Eric"], m3 == music_genres["classical"])
    ))
    
    # Clue 1: The person with child Fred is directly left of mystery book lover
    fred_house = z3.Int('fred_house')
    solver.add(z3.Or(
        z3.And(c1 == children["Fred"], fred_house == 1),
        z3.And(c2 == children["Fred"], fred_house == 2),
        z3.And(c3 == children["Fred"], fred_house == 3)
    ))
    solver.add(fred_house + 1 == mystery_house)
    
    # Clue 4: Science fiction book lover has child Meredith
    sf_house = z3.Int('sf_house')
    solver.add(z3.Or(
        z3.And(b1 == book_genres["science fiction"], sf_house == 1),
        z3.And(b2 == book_genres["science fiction"], sf_house == 2),
        z3.And(b3 == book_genres["science fiction"], sf_house == 3)
    ))
    solver.add(z3.Or(
        z3.And(sf_house == 1, c1 == children["Meredith"]),
        z3.And(sf_house == 2, c2 == children["Meredith"]),
        z3.And(sf_house == 3, c3 == children["Meredith"])
    ))
    
    # Clue 6: Rock music lover is right of romance book lover
    romance_house = z3.Int('romance_house')
    rock_house = z3.Int('rock_house')
    solver.add(z3.Or(
        z3.And(b1 == book_genres["romance"], romance_house == 1),
        z3.And(b2 == book_genres["romance"], romance_house == 2),
        z3.And(b3 == book_genres["romance"], romance_house == 3)
    ))
    solver.add(z3.Or(
        z3.And(m1 == music_genres["rock"], rock_house == 1),
        z3.And(m2 == music_genres["rock"], rock_house == 2),
        z3.And(m3 == music_genres["rock"], rock_house == 3)
    ))
    solver.add(rock_house > romance_house)
    
    # Check and get the model
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Map back integer values to strings
        rev_names = {v: k for k, v in names.items()}
        rev_music = {v: k for k, v in music_genres.items()}
        rev_children = {v: k for k, v in children.items()}
        rev_books = {v: k for k, v in book_genres.items()}
        
        # Collect values for each house
        houses = []
        for i in range(1, 4):
            n_val = model.eval(eval(f'n{i}')).as_long()
            m_val = model.eval(eval(f'm{i}')).as_long()
            c_val = model.eval(eval(f'c{i}')).as_long()
            b_val = model.eval(eval(f'b{i}')).as_long()
            
            houses.append([
                str(i),
                rev_names[n_val],
                rev_music[m_val],
                rev_children[c_val],
                rev_books[b_val]
            ])
        
        # Format the solution as JSON
        solution = {
            "solution": {
                "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                "rows": houses
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()