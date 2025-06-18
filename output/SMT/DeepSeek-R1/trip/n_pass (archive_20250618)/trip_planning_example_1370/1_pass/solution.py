from z3 import *
import json

def main():
    # Define city names and their required days
    city_names = ["Paris", "Krakow", "Vilnius", "Munich", "Geneva", "Amsterdam", "Budapest", "Split", "Santorini"]
    required_days = [5, 5, 3, 5, 2, 4, 5, 4, 5]  # Corresponding to the cities above

    # Define the directed flight edges
    edges = set()
    # Bidirectional edges: both directions
    bidirectional_pairs = [
        (0,1), (1,0),  # Paris and Krakow
        (0,5), (5,0),  # Paris and Amsterdam
        (0,7), (7,0),  # Paris and Split
        (0,4), (4,0),  # Paris and Geneva
        (5,4), (4,5),  # Amsterdam and Geneva
        (3,7), (7,3),  # Munich and Split
        (7,1), (1,7),  # Split and Krakow
        (3,5), (5,3),  # Munich and Amsterdam
        (6,5), (5,6),  # Budapest and Amsterdam
        (7,4), (4,7),  # Split and Geneva
        (2,7), (7,2),  # Vilnius and Split
        (2,5), (5,2),  # Vilnius and Amsterdam
        (6,0), (0,6),  # Budapest and Paris
        (1,5), (5,1),  # Krakow and Amsterdam
        (2,0), (0,2),  # Vilnius and Paris
        (6,4), (4,6),  # Budapest and Geneva
        (7,5), (5,7),  # Split and Amsterdam
        (8,4), (4,8),  # Santorini and Geneva
        (5,8), (8,5),  # Amsterdam and Santorini
        (3,6), (6,3),  # Munich and Budapest
        (3,0), (0,3),  # Munich and Paris
        (3,4), (4,3)   # Munich and Geneva
    ]
    for (u, v) in bidirectional_pairs:
        edges.add((u, v))
    # Directed edges
    edges.add((2, 3))  # Vilnius to Munich
    edges.add((1, 2))  # Krakow to Vilnius

    n_days = 30
    # Z3 variables for each day: city_start, flight (boolean), to_city (if flight)
    city_start = [Int('city_start_%d' % (d+1)) for d in range(n_days)]
    flight = [Bool('flight_%d' % (d+1)) for d in range(n_days)]
    to_city = [Int('to_city_%d' % (d+1)) for d in range(n_days)]

    solver = Solver()
    solver.set("timeout", 300000)  # 5 minutes timeout

    # Domain constraints for city_start and to_city: integers 0 to 8
    for d in range(n_days):
        solver.add(city_start[d] >= 0, city_start[d] <= 8)
        solver.add(to_city[d] >= 0, to_city[d] <= 8)

    # State transition: city_start for next day
    for d in range(n_days - 1):
        solver.add(city_start[d+1] == If(flight[d], to_city[d], city_start[d]))

    # Flight constraints: if flight, then (city_start, to_city) must be in edges and not the same city
    for d in range(n_days):
        # Condition: (city_start[d], to_city[d]) must be in edges if flight[d] is True
        edge_conds = []
        for (u, v) in edges:
            edge_conds.append(And(city_start[d] == u, to_city[d] == v))
        solver.add(Implies(flight[d], Or(edge_conds)))
        solver.add(Implies(flight[d], city_start[d] != to_city[d]))

    # Total days per city: sum over days of 1 if in the city (either as start or flight arrival)
    total_days_per_city = [0] * 9
    for c in range(9):
        total = 0
        for d in range(n_days):
            in_city = Or(city_start[d] == c, And(flight[d], to_city[d] == c))
            total += If(in_city, 1, 0)
        solver.add(total == required_days[c])

    # Total flights must be 8
    total_flights = Sum([If(flight[d], 1, 0) for d in range(n_days)])
    solver.add(total_flights == 8)

    # Meeting constraints
    # Santorini (city 8) between day 25 and 29 (inclusive): days 24 to 28 (0-indexed)
    santorini_days = []
    for d in range(24, 29):  # days 25 to 29: indices 24 to 28
        in_city = Or(city_start[d] == 8, And(flight[d], to_city[d] == 8))
        santorini_days.append(in_city)
    solver.add(Or(santorini_days))

    # Krakow (city 1) between day 18 and 22: days 17 to 21 (0-indexed)
    krakow_days = []
    for d in range(17, 22):  # days 18 to 22
        in_city = Or(city_start[d] == 1, And(flight[d], to_city[d] == 1))
        krakow_days.append(in_city)
    solver.add(Or(krakow_days))

    # Paris (city 0) between day 11 and 15: days 10 to 14 (0-indexed)
    paris_days = []
    for d in range(10, 15):  # days 11 to 15
        in_city = Or(city_start[d] == 0, And(flight[d], to_city[d] == 0))
        paris_days.append(in_city)
    solver.add(Or(paris_days))

    # Solve
    if solver.check() == sat:
        model = solver.model()
        # Evaluate the variables
        cs_val = [model.evaluate(city_start[d]).as_long() for d in range(n_days)]
        fl_val = [model.evaluate(flight[d]) for d in range(n_days)]
        tc_val = [model.evaluate(to_city[d]).as_long() for d in range(n_days)]

        # Build presence sets for each city
        presence = [set() for _ in range(9)]
        for d in range(n_days):
            day_num = d + 1
            start_city = cs_val[d]
            presence[start_city].add(day_num)
            if fl_val[d]:
                arrival_city = tc_val[d]
                presence[arrival_city].add(day_num)

        # Build the list for output: we have two types of records: 
        #   Type A: contiguous intervals for each city
        #   Type B: flight day records (single day for departure and arrival)
        records = []  # will be tuples (start_day, type0, record_dict)

        # Type A: contiguous intervals
        for c in range(9):
            if not presence[c]:
                continue
            days_sorted = sorted(presence[c])
            intervals = []
            start = days_sorted[0]
            end = start
            for i in range(1, len(days_sorted)):
                if days_sorted[i] == end + 1:
                    end = days_sorted[i]
                else:
                    intervals.append((start, end))
                    start = days_sorted[i]
                    end = start
            intervals.append((start, end))
            for (s, e) in intervals:
                if s == e:
                    day_str = "Day %d" % s
                else:
                    day_str = "Day %d-%d" % (s, e)
                record = {"day_range": day_str, "place": city_names[c]}
                records.append((s, 2, record))  # type2 for intervals

        # Type B: flight day records (for each flight day, two records: departure and arrival)
        for d in range(n_days):
            if fl_val[d]:
                day_num = d + 1
                dep_city = cs_val[d]
                arr_city = tc_val[d]
                # Departure record
                dep_record = {"day_range": "Day %d" % day_num, "place": city_names[dep_city]}
                records.append((day_num, 0, dep_record))  # type0 for departure
                # Arrival record
                arr_record = {"day_range": "Day %d" % day_num, "place": city_names[arr_city]}
                records.append((day_num, 1, arr_record))  # type1 for arrival

        # Sort records: by start_day (the first element of the tuple), then by type (0,1,2)
        records_sorted = sorted(records, key=lambda x: (x[0], x[1]))
        itinerary_list = [rec for (_, _, rec) in records_sorted]

        # Create the final JSON
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()