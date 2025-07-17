import z3

def main():
    # Define city indices
    cities = {
        "Brussels": 0,
        "Venice": 1,
        "London": 2,
        "Lisbon": 3,
        "Reykjavik": 4,
        "Santorini": 5,
        "Madrid": 6
    }
    city_names = {v: k for k, v in cities.items()}

    # Define allowed flights as directed edges
    symmetric_pairs = [
        (0, 1), (0, 2), (0, 3), (0, 4), (0, 6),
        (1, 5), (1, 3), (1, 2), (1, 6),
        (3, 4), (3, 2), (3, 6),
        (2, 5), (2, 4), (2, 6),
        (5, 6)
    ]
    allowed_flights = []
    for a, b in symmetric_pairs:
        allowed_flights.append((a, b))
        allowed_flights.append((b, a))
    allowed_flights.append((4, 6))  # Reykjavik to Madrid (directed)

    # Create Z3 variables for x and y for 17 days
    x = [z3.Int(f'x_{i}') for i in range(17)]  # x_i: city at start of day i+1
    y = [z3.Int(f'y_{i}') for i in range(17)]  # y_i: city at end of day i+1

    s = z3.Solver()

    # Fixed constraints: start in Brussels on day 1 and 2
    s.add(x[0] == cities["Brussels"])
    s.add(y[0] == cities["Brussels"])
    s.add(x[1] == cities["Brussels"])  # because y0 = x1

    # Constraint: next day's start is previous day's end
    for i in range(16):  # i from 0 to 15: for x[1] to x[16] (day2 to day17) and y[0] to y[15]
        s.add(x[i+1] == y[i])

    # Each city code must be between 0 and 6
    for i in range(17):
        s.add(x[i] >= 0, x[i] <= 6)
        s.add(y[i] >= 0, y[i] <= 6)

    # Flight constraints: for each day, either no flight or a direct flight exists
    for i in range(17):
        options = [x[i] == y[i]]  # no flight
        for a, b in allowed_flights:
            options.append(z3.And(x[i] == a, y[i] == b))
        s.add(z3.Or(options))

    # Total days per city
    total_days = [0] * 7  # for cities 0 to 6
    for c in range(7):
        # Count days where the city is at the start (x_i = c)
        part1 = z3.Sum([z3.If(x[i] == c, 1, 0) for i in range(17)])
        # Count days where a flight ends in the city (y_i = c and flight occurred: x_i != y_i)
        part2 = z3.Sum([z3.If(z3.And(x[i] != y[i], y[i] == c), 1, 0) for i in range(17)])
        total_days[c] = part1 + part2

    s.add(total_days[cities["Brussels"]] == 2)
    s.add(total_days[cities["Venice"]] == 3)
    s.add(total_days[cities["London"]] == 3)
    s.add(total_days[cities["Lisbon"]] == 4)
    s.add(total_days[cities["Reykjavik"]] == 3)
    s.add(total_days[cities["Santorini"]] == 3)
    s.add(total_days[cities["Madrid"]] == 5)

    # Venice must appear between day5 (index4) and day7 (index6)
    venice_constraints = []
    for i in [4, 5, 6]:  # days 5,6,7
        # Either at start of day or flight arrives on that day
        venice_constraints.append(z3.Or(x[i] == cities["Venice"], z3.And(x[i] != y[i], y[i] == cities["Venice"])))
    s.add(z3.Or(venice_constraints))

    # Madrid must appear between day7 (index6) and day11 (index10)
    madrid_constraints = []
    for i in [6, 7, 8, 9, 10]:  # days 7 to 11
        madrid_constraints.append(z3.Or(x[i] == cities["Madrid"], z3.And(x[i] != y[i], y[i] == cities["Madrid"])))
    s.add(z3.Or(madrid_constraints))

    # Check and get model
    if s.check() == z3.sat:
        model = s.model()
        x_vals = [model.evaluate(x_i).as_long() for x_i in x]
        y_vals = [model.evaluate(y_i).as_long() for y_i in y]
        
        # Build segments and flights
        segments = []  # (start_day, end_day, city_index)
        flights = []   # (day, from_city, to_city)
        current_city = x_vals[0]
        start_day = 1
        for i in range(17):
            if y_vals[i] != x_vals[i]:  # flight at the end of day i+1
                end_day = i + 1
                segments.append((start_day, end_day, current_city))
                flights.append((end_day, current_city, y_vals[i]))
                current_city = y_vals[i]
                start_day = end_day
        segments.append((start_day, 17, current_city))
        
        # Build itinerary
        itinerary = []
        for j in range(len(flights)):
            s, e, c = segments[j]
            if s == e:
                day_range_str = f"Day {s}"
            else:
                day_range_str = f"Day {s}-{e}"
            itinerary.append({"day_range": day_range_str, "place": city_names[c]})
            
            d, fr, to = flights[j]
            itinerary.append({"day_range": f"Day {d}", "place": city_names[fr]})
            itinerary.append({"day_range": f"Day {d}", "place": city_names[to]})
        
        # Last segment
        s, e, c = segments[-1]
        if s == e:
            day_range_str = f"Day {s}"
        else:
            day_range_str = f"Day {s}-{e}"
        itinerary.append({"day_range": day_range_str, "place": city_names[c]})
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()