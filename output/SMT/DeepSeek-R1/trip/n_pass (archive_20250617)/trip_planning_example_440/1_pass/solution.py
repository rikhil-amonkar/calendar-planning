from z3 import *

def main():
    # City indices
    Split = 0
    Helsinki = 1
    Reykjavik = 2
    Vilnius = 3
    Geneva = 4

    city_names = {
        0: "Split",
        1: "Helsinki",
        2: "Reykjavik",
        3: "Vilnius",
        4: "Geneva"
    }

    # Allowed flight pairs (both directions)
    edges = [
        (Split, Helsinki),
        (Geneva, Split),
        (Geneva, Helsinki),
        (Helsinki, Reykjavik),
        (Vilnius, Helsinki),
        (Split, Vilnius)
    ]
    allowed_pairs = []
    for u, v in edges:
        allowed_pairs.append((u, v))
        allowed_pairs.append((v, u))

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
        or_conditions = []
        for u, v in allowed_pairs:
            or_conditions.append(And(city_in[d] == u, city_out[d] == v))
        s.add(Implies(fly[d], Or(or_conditions)))

    # Continuity constraints
    for d in range(days - 1):
        s.add(city_out[d] == city_in[d + 1])

    # Total days per city
    total_days = [0] * 5
    for c in range(5):
        total = 0
        for d in range(days):
            total += If(Or(city_in[d] == c, city_out[d] == c), 1, 0)
        s.add(total == [2, 2, 3, 3, 6][c])

    # Event constraints
    rey_days = []
    for d in [9, 10, 11]:  # Days 10, 11, 12
        rey_days.append(Or(city_in[d] == Reykjavik, city_out[d] == Reykjavik))
    s.add(Or(rey_days))

    vil_days = []
    for d in [6, 7, 8]:  # Days 7, 8, 9
        vil_days.append(Or(city_in[d] == Vilnius, city_out[d] == Vilnius))
    s.add(Or(vil_days))

    # Solve and output
    if s.check() == sat:
        m = s.model()
        plan = []
        for d in range(days):
            in_city_val = m.eval(city_in[d]).as_long()
            out_city_val = m.eval(city_out[d]).as_long()
            fly_val = m.eval(fly[d])
            plan.append((d + 1, in_city_val, out_city_val, fly_val))
        
        print("Day-by-Day Plan:")
        for day, in_city, out_city, is_fly in plan:
            if is_fly:
                print(f"Day {day}: Fly from {city_names[in_city]} to {city_names[out_city]} (present in both {city_names[in_city]} and {city_names[out_city]})")
            else:
                print(f"Day {day}: Stay in {city_names[in_city]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()