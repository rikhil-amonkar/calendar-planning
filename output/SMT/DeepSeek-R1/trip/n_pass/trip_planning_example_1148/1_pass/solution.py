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

    # Recurrence for start days
    for i in range(1, 8):
        d_expr = If(
            city[i-1] == Tallinn, durations[Tallinn],
            If(city[i-1] == Stockholm, durations[Stockholm],
            If(city[i-1] == Copenhagen, durations[Copenhagen],
            If(city[i-1] == Prague, durations[Prague],
            If(city[i-1] == Lisbon, durations[Lisbon],
            If(city[i-1] == Dubrovnik, durations[Dubrovnik],
            If(city[i-1] == Split, durations[Split],
                durations[Lyon]))))))
        s.add(start[i] == start[i-1] + d_expr - 1)

    # Constraints for Tallinn: start day must be 1 or 2
    tallinn_const = Or([And(city[i] == Tallinn, Or(start[i] == 1, start[i] == 2)) for i in range(8)])
    s.add(tallinn_const)

    # Constraints for Lisbon: start day must be 3, 4, or 5
    lisbon_const = Or([And(city[i] == Lisbon, Or(start[i] == 3, start[i] == 4, start[i] == 5)) for i in range(8)])
    s.add(lisbon_const)

    # Constraints for Stockholm: start day between 10 and 16 inclusive
    stockholm_const = Or([And(city[i] == Stockholm, And(start[i] >= 10, start[i] <= 16)) for i in range(8)])
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
            d_val = durations[c_index]
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