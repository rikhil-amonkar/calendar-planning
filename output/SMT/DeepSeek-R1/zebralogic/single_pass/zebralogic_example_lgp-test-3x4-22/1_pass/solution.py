from z3 import *

def main():
    # Create solver
    s = Solver()

    # Define the attributes for three houses (index 0: house1, index1: house2, index2: house3)
    n = [Int('n0'), Int('n1'), Int('n2')]  # Name: 0=Arnold, 1=Eric, 2=Peter
    m = [Int('m0'), Int('m1'), Int('m2')]  # Music: 0=pop, 1=rock, 2=classical
    c = [Int('c0'), Int('c1'), Int('c2')]  # Child: 0=Fred, 1=Meredith, 2=Bella
    b = [Int('b0'), Int('b1'), Int('b2')]  # Book: 0=mystery, 1=romance, 2=science fiction

    # Each attribute must be between 0 and 2 (inclusive)
    for i in range(3):
        s.add(n[i] >= 0, n[i] <= 2)
        s.add(m[i] >= 0, m[i] <= 2)
        s.add(c[i] >= 0, c[i] <= 2)
        s.add(b[i] >= 0, b[i] <= 2)

    # All attributes must be distinct in their category
    s.add(Distinct(n))
    s.add(Distinct(m))
    s.add(Distinct(c))
    s.add(Distinct(b))

    # Clue 1: The person's child is named Fred is directly left of the person who loves mystery books.
    s.add(Or(
        And(c[0] == 0, b[1] == 0),  # Fred in house1, mystery in house2
        And(c[1] == 0, b[2] == 0)   # Fred in house2, mystery in house3
    ))

    # Clue 2: Peter is in the first house.
    s.add(n[0] == 2)  # Peter is 2

    # Clue 3: The person who loves mystery books is the person who loves classical music.
    # For the house with mystery books (b[i]==0), the music must be classical (m[i]==2)
    for i in range(3):
        s.add(If(b[i] == 0, m[i] == 2, True))

    # Clue 4: The person who loves science fiction books is the person's child is named Meredith.
    # For the house with science fiction books (b[i]==2), the child must be Meredith (c[i]==1)
    for i in range(3):
        s.add(If(b[i] == 2, c[i] == 1, True))

    # Clue 5: Eric is the person who loves mystery books.
    # So the house where name is Eric (n[i]==1) must have book genre mystery (b[i]==0)
    for i in range(3):
        s.add(If(n[i] == 1, b[i] == 0, True))

    # Clue 6: The person who loves rock music is somewhere to the right of the person who loves romance books.
    # So there exists a house i with romance books (b[i]==1) and a house j with rock music (m[j]==1) such that j > i.
    s.add(Or(
        And(b[0] == 1, m[1] == 1),  # romance in house1, rock in house2
        And(b[0] == 1, m[2] == 1),  # romance in house1, rock in house3
        And(b[1] == 1, m[2] == 1)    # romance in house2, rock in house3
    ))

    # Check for solution
    if s.check() == sat:
        model = s.model()
        # Map the integer values back to strings
        name_map = {0: 'Arnold', 1: 'Eric', 2: 'Peter'}
        music_map = {0: 'pop', 1: 'rock', 2: 'classical'}
        child_map = {0: 'Fred', 1: 'Meredith', 2: 'Bella'}
        book_map = {0: 'mystery', 1: 'romance', 2: 'science fiction'}

        # Prepare the rows for the output
        rows = []
        for i in range(3):
            house = str(i+1)
            name_val = model.eval(n[i]).as_long()
            music_val = model.eval(m[i]).as_long()
            child_val = model.eval(c[i]).as_long()
            book_val = model.eval(b[i]).as_long()
            row = [
                house,
                name_map[name_val],
                music_map[music_val],
                child_map[child_val],
                book_map[book_val]
            ]
            rows.append(row)

        # Create the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                "rows": rows
            }
        }

        # Print as JSON
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()