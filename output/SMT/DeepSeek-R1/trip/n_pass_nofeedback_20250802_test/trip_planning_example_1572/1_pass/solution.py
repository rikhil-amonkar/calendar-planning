import z3

def main():
    # Fixed cities: positions 0: Berlin, 8: Stockholm, 9: Riga
    # Assignment for positions 1 to 7 (city2 to city8) from the list of 7 cities
    city_names = ["Paris", "Zurich", "Lyon", "Seville", "Milan", "Naples", "Nice"]
    city_durations = [5, 5, 3, 3, 3, 4, 2]
    n = 7  # number of cities to assign

    # Flight pairs as a set of tuples (city1, city2)
    flight_pairs = [
        ("Paris", "Stockholm"), ("Seville", "Paris"), ("Naples", "Zurich"), ("Nice", "Riga"),
        ("Berlin", "Milan"), ("Paris", "Zurich"), ("Paris", "Nice"), ("Milan", "Paris"),
        ("Milan", "Riga"), ("Paris", "Lyon"), ("Milan", "Naples"), ("Paris", "Riga"),
        ("Berlin", "Stockholm"), ("Stockholm", "Riga"), ("Nice", "Zurich"), ("Milan", "Zurich"),
        ("Lyon", "Nice"), ("Zurich", "Stockholm"), ("Zurich", "Riga"), ("Berlin", "Naples"),
        ("Milan", "Stockholm"), ("Berlin", "Zurich"), ("Milan", "Seville"), ("Paris", "Naples"),
        ("Berlin", "Riga"), ("Nice", "Stockholm"), ("Berlin", "Paris"), ("Nice", "Naples"),
        ("Berlin", "Nice")
    ]
    flight_set = set()
    for a, b in flight_pairs:
        flight_set.add((a, b))
        flight_set.add((b, a))

    # Build allowed matrix for the 7 cities: [i][j] = 1 if flight between city_names[i] and city_names[j]
    allowed = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if (city_names[i], city_names[j]) in flight_set:
                allowed[i][j] = 1

    # Berlin to any of the 7 cities
    berlin_allowed = [0] * n
    for i in range(n):
        if ("Berlin", city_names[i]) in flight_set:
            berlin_allowed[i] = 1

    # Any of the 7 cities to Stockholm
    stockholm_allowed = [0] * n
    for i in range(n):
        if (city_names[i], "Stockholm") in flight_set:
            stockholm_allowed[i] = 1

    # Define variables for assignment: c[0] to c[6] for the 7 positions (city2 to city8)
    s = z3.Solver()
    c = [z3.Int('c_%i' % i) for i in range(n)]
    for i in range(n):
        s.add(c[i] >= 0, c[i] < n)
    s.add(z3.Distinct(c))

    # Duration for each assigned city
    d = [None] * n
    for i in range(n):
        d[i] = z3.If(c[i] == 0, 5,
                z3.If(c[i] == 1, 5,
                z3.If(c[i] == 2, 3,
                z3.If(c[i] == 3, 3,
                z3.If(c[i] == 4, 3,
                z3.If(c[i] == 5, 4, 2))))))

    # Start days for the 7 assigned cities (city2 to city8)
    start_days = [z3.Int('s_%i' % i) for i in range(n)]
    s.add(start_days[0] == 2)  # city2 starts on day2

    for i in range(1, n):
        s.add(start_days[i] == start_days[i-1] + d[i-1] - 1)

    # Constraint: the last assigned city (city8) must end on day 20 (so that city9 starts on day20)
    s.add(start_days[n-1] + d[n-1] - 1 == 20)

    # Constraint for Nice: must start on day12
    # Nice is represented by index 6 in city_names
    nice_constraint = z3.Or(*[z3.And(c[i] == 6, start_days[i] == 12) for i in range(n)])
    s.add(nice_constraint)

    # Flight constraints
    # From Berlin to the first assigned city (c[0])
    s.add(z3.Or(*[z3.And(c[0] == i, berlin_allowed[i] == 1) for i in range(n)]))

    # Between consecutive assigned cities
    for i in range(n-1):
        s.add(z3.Or(*[z3.And(c[i] == idx_i, c[i+1] == idx_j) 
                    for idx_i in range(n) for idx_j in range(n) 
                    if allowed[idx_i][idx_j] == 1]))

    # From the last assigned city (c[6]) to Stockholm
    s.add(z3.Or(*[z3.And(c[6] == i, stockholm_allowed[i] == 1) for i in range(n)]))

    # Check and get model
    if s.check() == z3.sat:
        model = s.model()
        c_val = [model.evaluate(c[i]).as_long() for i in range(n)]
        d_val = [city_durations[c_val[i]] for i in range(n)]
        start_days_val = [model.evaluate(start_days[i]).as_long() for i in range(n)]

        # Start days for all 10 cities
        all_starts = [1]  # Berlin
        all_starts.append(2)  # city2
        for i in range(1, n):
            all_starts.append(start_days_val[i])
        all_starts.append(20)  # Stockholm
        all_starts.append(22)  # Riga

        all_durations = [2]  # Berlin
        for i in range(n):
            all_durations.append(d_val[i])
        all_durations.extend([3, 2])  # Stockholm, Riga

        all_city_names = ["Berlin"]
        for i in range(n):
            all_city_names.append(city_names[c_val[i]])
        all_city_names.append("Stockholm")
        all_city_names.append("Riga")

        # Build itinerary for 23 days
        itinerary = []
        for day in range(1, 24):
            places = []
            for i in range(10):
                start = all_starts[i]
                end = start + all_durations[i] - 1
                if start <= day <= end:
                    places.append(all_city_names[i])
            places.sort()
            place_str = ", ".join(places)
            itinerary.append({"day": day, "place": place_str})

        # Output as JSON
        import json
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()