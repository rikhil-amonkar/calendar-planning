import z3
import json

def main():
    # Create solver
    s = z3.Solver()

    # Cities: 0: Vienna, 1: Nice, 2: Stockholm, 3: Split
    n_days = 10  # c1 to c10
    c = [z3.Int(f'c_{i}') for i in range(1, 11)]
    f = [z3.Bool(f'f_{i}') for i in range(1, 10)]

    # Constraint: Start in Vienna on Day 1 and Day 2
    s.add(c[0] == 0)
    s.add(c[1] == 0)

    # Domain for c: 0 to 3
    for i in range(10):
        s.add(z3.Or(c[i] == 0, c[i] == 1, c[i] == 2, c[i] == 3))

    # Valid direct flight pairs (symmetric)
    valid_pairs = [
        (0, 1), (1, 0),
        (0, 2), (2, 0),
        (0, 3), (3, 0),
        (1, 2), (2, 1),
        (2, 3), (3, 2)
    ]

    # Flight constraints for days 1 to 9
    for d in range(9):
        # If flight on day d+1, ensure valid pair; otherwise, same city next day
        s.add(z3.If(f[d],
            z3.Or([z3.And(c[d] == a, c[d+1] == b) for (a, b) in valid_pairs]),
            c[d] == c[d+1]
        ))

    # Exactly 3 flights
    s.add(z3.Sum([z3.If(f_i, 1, 0) for f_i in f]) == 3)

    # Count days in each city
    vienna_days = z3.Int('vienna_days')
    nice_days = z3.Int('nice_days')
    stockholm_days = z3.Int('stockholm_days')
    split_days = z3.Int('split_days')

    # Initialize counters
    v_count = 0
    n_count = 0
    st_count = 0
    sp_count = 0

    for d in range(9):  # Days 1 to 9
        # Vienna
        v_count += z3.If(z3.Or(c[d] == 0, z3.And(f[d], c[d+1] == 0)), 1, 0)
        # Nice
        n_count += z3.If(z3.Or(c[d] == 1, z3.And(f[d], c[d+1] == 1)), 1, 0)
        # Stockholm
        st_count += z3.If(z3.Or(c[d] == 2, z3.And(f[d], c[d+1] == 2)), 1, 0)
        # Split
        sp_count += z3.If(z3.Or(c[d] == 3, z3.And(f[d], c[d+1] == 3)), 1, 0)

    s.add(v_count == 2, n_count == 2, st_count == 5, sp_count == 3)

    # Split on Day 7 and Day 9
    s.add(z3.Or(c[6] == 3, z3.And(f[6], c[7] == 3)))  # Day 7
    s.add(z3.Or(c[8] == 3, z3.And(f[8], c[9] == 3)))  # Day 9

    # Check for solution
    if s.check() == z3.sat:
        model = s.model()
        c_val = [model.evaluate(c[i]).as_long() for i in range(10)]
        f_val = [z3.is_true(model.evaluate(f[i])) for i in range(9)]
        city_names = ["Vienna", "Nice", "Stockholm", "Split"]
        
        # Track presence of each city per day (1 to 9)
        present = {city: set() for city in city_names}
        for d in range(9):  # Days 1 to 9
            day_index = d
            city_at_start = city_names[c_val[day_index]]
            present[city_at_start].add(d+1)
            if f_val[d]:
                next_city = city_names[c_val[day_index+1]]
                present[next_city].add(d+1)
        
        # Generate contiguous blocks for each city
        contiguous_blocks = []
        for city in city_names:
            days = sorted(present[city])
            if not days:
                continue
            start = days[0]
            end = days[0]
            blocks = []
            for i in range(1, len(days)):
                if days[i] == end + 1:
                    end = days[i]
                else:
                    blocks.append((start, end, city))
                    start = days[i]
                    end = days[i]
            blocks.append((start, end, city))
            contiguous_blocks.extend(blocks)
        
        # Sort blocks by start day
        contiguous_blocks.sort(key=lambda x: x[0])
        
        # Prepare flight records: for each flight day, both cities
        flight_dict = {}
        for d in range(9):
            if f_val[d]:
                dep_city = city_names[c_val[d]]
                arr_city = city_names[c_val[d+1]]
                flight_dict[d+1] = [dep_city, arr_city]
        
        # Build itinerary
        itinerary = []
        for block in contiguous_blocks:
            start, end, city = block
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
            if end in flight_dict:
                for city_flight in flight_dict[end]:
                    itinerary.append({"day_range": f"Day {end}", "place": city_flight})
                del flight_dict[end]  # Avoid duplicate
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()