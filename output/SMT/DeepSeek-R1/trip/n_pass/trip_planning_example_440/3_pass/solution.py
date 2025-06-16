from z3 import *

def main():
    # City indices
    Split = 0
    Helsinki = 1
    Reykjavik = 2
    Vilnius = 3
    Geneva = 4

    city_names = {
        Split: "Split",
        Helsinki: "Helsinki",
        Reykjavik: "Reykjavik",
        Vilnius: "Vilnius",
        Geneva: "Geneva"
    }

    # Allowed flight pairs (bidirectional)
    allowed_pairs = [
        (Split, Helsinki),
        (Geneva, Split),
        (Geneva, Helsinki),
        (Helsinki, Reykjavik),
        (Vilnius, Helsinki),
        (Split, Vilnius)
    ]
    # Add both directions
    allowed_pairs += [(v, u) for (u, v) in allowed_pairs]

    s = Solver()
    days = 12

    # Variables for each day
    city_in = [Int(f'city_in_{d+1}') for d in range(days)]
    city_out = [Int(f'city_out_{d+1}') for d in range(days)]
    fly = [Bool(f'fly_{d+1}') for d in range(days)]

    # Domain constraints
    for d in range(days):
        s.add(city_in[d] >= 0, city_in[d] <= 4)
        s.add(city_out[d] >= 0, city_out[d] <= 4)

    # Flight constraints
    for d in range(days):
        s.add(fly[d] == (city_in[d] != city_out[d]))
        # Valid flight only if pair is allowed
        valid_flight = Or([And(city_in[d] == u, city_out[d] == v) for u, v in allowed_pairs])
        s.add(Implies(fly[d], valid_flight))

    # Continuity between days
    for d in range(days - 1):
        s.add(city_out[d] == city_in[d + 1])

    # Start in Geneva
    s.add(city_in[0] == Geneva)

    # Total days per city (counting flying days in both cities)
    city_totals = [0] * 5
    for c in range(5):
        total = 0
        for d in range(days):
            total += If(Or(city_in[d] == c, city_out[d] == c), 1, 0)
        s.add(total == [2, 2, 3, 3, 6][c])

    # Event constraints: at least one full day in event window
    # Vilnius: days 7-9 (indices 6-8)
    vil_full_day = Or([And(city_in[d] == Vilnius, city_out[d] == Vilnius) for d in [6, 7, 8]])
    s.add(vil_full_day)

    # Reykjavik: days 10-12 (indices 9-11)
    rey_full_day = Or([And(city_in[d] == Reykjavik, city_out[d] == Reykjavik) for d in [9, 10, 11]])
    s.add(rey_full_day)

    # Solve and print plan
    if s.check() == sat:
        m = s.model()
        print("Day-by-Day Plan:")
        for d in range(days):
            in_city = m.eval(city_in[d]).as_long()
            out_city = m.eval(city_out[d]).as_long()
            is_fly = m.eval(fly[d])
            if is_fly:
                print(f"Day {d+1}: Fly from {city_names[in_city]} to {city_names[out_city]} (present in both {city_names[in_city]} and {city_names[out_city]})")
            else:
                print(f"Day {d+1}: Stay in {city_names[in_city]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()