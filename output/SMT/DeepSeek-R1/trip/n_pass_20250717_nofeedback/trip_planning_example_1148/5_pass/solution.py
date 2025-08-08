from z3 import *
import json

def main():
    # City indices
    Tallinn = 0
    Stockholm = 1
    Copenhagen = 2
    Prague = 3
    Lisbon = 4
    Dubrovnik = 5
    Split = 6
    Lyon = 7

    city_names = {
        Tallinn: 'Tallinn',
        Stockholm: 'Stockholm',
        Copenhagen: 'Copenhagen',
        Prague: 'Prague',
        Lisbon: 'Lisbon',
        Dubrovnik: 'Dubrovnik',
        Split: 'Split',
        Lyon: 'Lyon'
    }

    durations = [2, 4, 5, 3, 2, 5, 3, 2]  # Indexed by city

    # Allowed directed flight pairs
    undirected_edges = [
        (Dubrovnik, Stockholm),
        (Lisbon, Copenhagen),
        (Lisbon, Lyon),
        (Copenhagen, Stockholm),
        (Copenhagen, Split),
        (Prague, Stockholm),
        (Tallinn, Stockholm),
        (Prague, Lyon),
        (Lisbon, Stockholm),
        (Prague, Lisbon),
        (Stockholm, Split),
        (Prague, Copenhagen),
        (Split, Lyon),
        (Copenhagen, Dubrovnik),
        (Prague, Split),
        (Tallinn, Copenhagen),
        (Tallinn, Prague)
    ]
    allowed_pairs = set()
    for (a, b) in undirected_edges:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))

    s = Solver()

    # 8 positions, each holds a city index (0-7)
    city = [Int(f'city_{i}') for i in range(8)]
    for i in range(8):
        s.add(city[i] >= 0, city[i] <= 7)
    s.add(Distinct(city))

    # Start days for each position
    start = [Int(f'start_{i}') for i in range(8)]
    s.add(start[0] == 1)  # First city starts on day 1
    s.add(city[7] == Lyon)  # Last city is Lyon
    s.add(start[7] == 18)   # Lyon starts on day 18

    # Fix Tallinn as first city to cover days 1-2
    s.add(city[0] == Tallinn)

    # Create duration array for Z3
    dur_arr = Array('dur_arr', IntSort(), IntSort())
    for i, d in enumerate(durations):
        s.add(dur_arr[i] == d)

    # Recurrence for start days: start[i] = start[i-1] + duration(city[i-1]) - 1
    for i in range(1, 8):
        d_expr = dur_arr[city[i-1]]
        s.add(start[i] == start[i-1] + d_expr - 1)

    # Constraints for Lisbon: must start on day 4 to cover event days 4-5
    lisbon_const = Or([And(city[i] == Lisbon, start[i] == 4) for i in range(8)])
    s.add(lisbon_const)

    # Constraints for Stockholm: must start on day 13 to cover event days 13-16
    stockholm_const = Or([And(city[i] == Stockholm, start[i] == 13) for i in range(8)])
    s.add(stockholm_const)

    # Flight constraints: consecutive cities must have a direct flight
    for i in range(7):
        a = city[i]
        b = city[i+1]
        constraints = []
        for (x, y) in allowed_pairs:
            constraints.append(And(a == x, b == y))
        s.add(Or(constraints))

    if s.check() == sat:
        m = s.model()
        city_order = [m.evaluate(city[i]).as_long() for i in range(8)]
        start_days = [m.evaluate(start[i]).as_long() for i in range(8)]
        
        intervals = []
        for i in range(8):
            c_index = city_order[i]
            s_day = start_days[i]
            d_val = durations[c_index]  # Use predefined duration
            e_day = s_day + d_val - 1
            city_name = city_names[c_index]
            intervals.append((city_name, s_day, e_day))
        
        itinerary_list = []
        for d in range(1, 20):
            cities_on_d = []
            for (name, s_val, e_val) in intervals:
                if s_val <= d <= e_val:
                    cities_on_d.append(name)
            itinerary_list.append({"day": d, "cities": cities_on_d})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()