from z3 import *

def main():
    # Define the variables
    T1 = Int('T1')
    T2 = Int('T2')
    s1 = Int('s1')  # Segment 1 city index
    s2 = Int('s2')  # Segment 2 city index
    s3 = Int('s3')  # Segment 3 city index

    # City names and their required days
    city_names = ["Vilnius", "Munich", "Mykonos"]
    days_required = [4, 3, 7]
    available_pairs = [(0, 1), (1, 0), (1, 2), (2, 1)]  # Allowed flight connections

    s = Solver()

    # Constraints for city indices (0, 1, 2) and distinct
    s.add(s1 >= 0, s1 <= 2)
    s.add(s2 >= 0, s2 <= 2)
    s.add(s3 >= 0, s3 <= 2)
    s.add(Distinct(s1, s2, s3))

    # Constraints for travel days
    s.add(T1 >= 1, T1 <= 12)
    s.add(T2 >= 2, T2 <= 12)
    s.add(T1 < T2)

    # Segment day constraints
    s.add(T1 == days_required[s1])
    s.add(T2 - T1 + 1 == days_required[s2])
    s.add(13 - T2 == days_required[s3])

    # Flight connection constraints
    s.add(Or([And(s1 == i, s2 == j) for (i, j) in available_pairs]))
    s.add(Or([And(s2 == i, s3 == j) for (i, j) in available_pairs]))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        t1_val = m.eval(T1).as_long()
        t2_val = m.eval(T2).as_long()
        s1_val = m.eval(s1).as_long()
        s2_val = m.eval(s2).as_long()
        s3_val = m.eval(s3).as_long()

        city1 = city_names[s1_val]
        city2 = city_names[s2_val]
        city3 = city_names[s3_val]

        itinerary = [
            {"day_range": f"Day 1-{t1_val}", "place": city1},
            {"day_range": f"Day {t1_val}", "place": city1},
            {"day_range": f"Day {t1_val}", "place": city2},
            {"day_range": f"Day {t1_val}-{t2_val}", "place": city2},
            {"day_range": f"Day {t2_val}", "place": city2},
            {"day_range": f"Day {t2_val}", "place": city3},
            {"day_range": f"Day {t2_val}-12", "place": city3}
        ]

        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No valid itinerary found.")

if __name__ == "__main__":
    main()