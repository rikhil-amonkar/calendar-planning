import z3

def main():
    # Define cities as indices
    city_to_index = {
        'Prague': 0,
        'Stuttgart': 1,
        'Split': 2,
        'Krakow': 3,
        'Florence': 4
    }
    index_to_city = {v: k for k, v in city_to_index.items()}

    # Allowed flights as pairs of indices
    allowed_pairs = [
        (0,1), (1,0),
        (0,4), (4,0),
        (3,1), (1,3),
        (3,2), (2,3),
        (2,0), (0,2),
        (3,0), (0,3),
    ]

    # Create 8 variables for each day (0-based index for days 1-8)
    days = [z3.Int(f'day_{i+1}') for i in range(8)]

    s = z3.Solver()

    # Each day must be a valid city index (0-4)
    for d in days:
        s.add(z3.And(0 <= d, d <= 4))

    # Day 2 (index 1) must be Stuttgart (1)
    s.add(days[1] == 1)

    # Day 3 (index 2) must be Split (2)
    s.add(days[2] == 2)

    # Consecutive transitions must be allowed if different
    for i in range(7):
        a = days[i]
        b = days[i+1]
        # If a != b, then (a, b) must be in allowed_pairs
        allowed = z3.Or([z3.And(a == x, b == y) for (x, y) in allowed_pairs])
        s.add(z3.Implies(a != b, allowed))

    required_days = [4, 2, 2, 2, 2]  # Prague, Stuttgart, Split, Krakow, Florence

    for c in range(5):
        count_in_days = z3.Sum([z3.If(days[i] == c, 1, 0) for i in range(8)])
        number_of_flights_originating = z3.Sum([
            z3.If(
                z3.And(
                    days[j] == c,
                    days[j] != days[j+1],
                    z3.Or([z3.And(c == x, days[j+1] == y) for (x, y) in allowed_pairs])
                ),
                1,
                0
            ) for j in range(7)
        ])
        total = count_in_days + number_of_flights_originating
        s.add(total == required_days[c])

    if s.check() == z3.sat:
        model = s.model()
        # Extract the days
        day_values = [model.evaluate(days[i]).as_long() for i in range(8)]
        # Convert to city names
        itinerary = []
        for day_num in range(1, 9):
            city_idx = day_values[day_num - 1]
            city_name = index_to_city[city_idx]
            itinerary.append({'day': day_num, 'city': city_name})
        # Format as JSON
        import json
        print(json.dumps({'itinerary': itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()