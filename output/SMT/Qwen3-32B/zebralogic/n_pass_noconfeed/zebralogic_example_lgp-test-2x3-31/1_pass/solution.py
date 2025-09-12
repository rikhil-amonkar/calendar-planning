import z3
import json

def main():
    s = z3.Solver()

    # Variables for each house's attributes
    name_1 = z3.Int('name_1')
    name_2 = z3.Int('name_2')

    sport_1 = z3.Int('sport_1')
    sport_2 = z3.Int('sport_2')

    hobby_1 = z3.Int('hobby_1')
    hobby_2 = z3.Int('hobby_2')

    # Uniqueness constraints
    s.add(name_1 != name_2)
    s.add(sport_1 != sport_2)
    s.add(hobby_1 != hobby_2)

    # Clue 1: Arnold's hobby is gardening. So (name == Arnold) <-> (hobby == gardening)
    s.add((name_1 == 1) == (hobby_1 == 1))
    s.add((name_2 == 1) == (hobby_2 == 1))

    # Clue 2: photography enthusiast is not in the first house
    s.add(hobby_1 == 1)

    # Clue 3: soccer lover is not in the first house
    s.add(sport_1 == 0)

    if s.check() == z3.sat:
        m = s.model()

        # Extract values for house 1
        n1 = m[name_1].as_long()
        s1 = m[sport_1].as_long()
        h1 = m[hobby_1].as_long()

        # House 2
        n2 = m[name_2].as_long()
        s2 = m[sport_2].as_long()
        h2 = m[hobby_2].as_long()

        # Map to strings
        def get_name(v): return 'Arnold' if v == 1 else 'Eric'
        def get_sport(v): return 'basketball' if v == 0 else 'soccer'
        def get_hobby(v): return 'photography' if v == 0 else 'gardening'

        rows = [
            ["1", get_name(n1), get_sport(s1), get_hobby(h1)],
            ["2", get_name(n2), get_sport(s2), get_hobby(h2)]
        ]

        solution = {
            "solution": {
                "header": ["House", "Name", "FavoriteSport", "Hobby"],
                "rows": rows
            }
        }

        print(json.dumps(solution))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()