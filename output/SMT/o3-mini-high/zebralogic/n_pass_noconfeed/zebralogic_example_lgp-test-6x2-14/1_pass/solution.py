import json
from z3 import *

def main():
    s = Solver()

    # Define person variables representing house positions (1 to 6)
    Peter   = Int('Peter')
    Bob     = Int('Bob')
    Eric    = Int('Eric')
    Carol   = Int('Carol')
    Arnold  = Int('Arnold')
    Alice   = Int('Alice')
    persons = [Peter, Bob, Eric, Carol, Arnold, Alice]

    # Define cigar variables representing house positions (1 to 6)
    blends         = Int('blends')
    yellow_monster = Int('yellow_monster')
    pall_mall      = Int('pall_mall')
    blue_master    = Int('blue_master')
    dunhill        = Int('dunhill')
    prince         = Int('prince')
    cigars = [blends, yellow_monster, pall_mall, blue_master, dunhill, prince]

    # Domain constraints: All houses are numbered 1 to 6
    for p in persons:
        s.add(And(p >= 1, p <= 6))
    for c in cigars:
        s.add(And(c >= 1, c <= 6))

    # All persons and cigars must occupy distinct houses
    s.add(Distinct(*persons))
    s.add(Distinct(*cigars))

    # Clue 8: Peter is in the first house.
    s.add(Peter == 1)
    # Clue 6: Eric is in the sixth house.
    s.add(Eric == 6)
    # Clue 9: Bob is in the third house.
    s.add(Bob == 3)

    # Clue 2: The person who smokes Blue Master is in the fifth house.
    s.add(blue_master == 5)
    # Clue 5: The person partial to Pall Mall is in the third house.
    s.add(pall_mall == 3)

    # Clue 7: Carol and Eric are next to each other.
    s.add(Or(Carol == Eric + 1, Carol == Eric - 1))

    # Clue 1: Arnold is somewhere to the left of the person who smokes many unique blends.
    # Here "many unique blends" refers to the cigar 'blends'.
    s.add(Arnold < blends)

    # Clue 3: Arnold is somewhere to the left of the Prince smoker.
    s.add(Arnold < prince)

    # Clue 4: There is one house between the person who smokes Yellow Monster and the person who smokes many unique blends.
    s.add(Abs(yellow_monster - blends) == 2)

    if s.check() == sat:
        m = s.model()
        # Build mappings of person names and cigars to their house numbers.
        person_positions = {
            "Peter": m[Peter].as_long(),
            "Bob": m[Bob].as_long(),
            "Eric": m[Eric].as_long(),
            "Carol": m[Carol].as_long(),
            "Arnold": m[Arnold].as_long(),
            "Alice": m[Alice].as_long()
        }
        cigar_positions = {
            "blends": m[blends].as_long(),
            "yellow monster": m[yellow_monster].as_long(),
            "pall mall": m[pall_mall].as_long(),
            "blue master": m[blue_master].as_long(),
            "dunhill": m[dunhill].as_long(),
            "prince": m[prince].as_long()
        }

        # Create the solution rows based on house order 1 to 6.
        rows = []
        for house in range(1, 7):
            house_name = None
            house_cigar = None
            for name, pos in person_positions.items():
                if pos == house:
                    house_name = name
                    break
            for cigar, pos in cigar_positions.items():
                if pos == house:
                    house_cigar = cigar
                    break
            rows.append([str(house), house_name, house_cigar])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()