from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 'Stockholm',
              'Istanbul', 'Amsterdam', 'Vienna', 'Split']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}

    # Direct flight connections (bidirectional)
    flight_pairs = [
        ('Riga', 'Stockholm'), ('Stockholm', 'Brussels'), ('Istanbul', 'Munich'),
        ('Istanbul', 'Riga'), ('Prague', 'Split'), ('Vienna', 'Brussels'),
        ('Vienna', 'Riga'), ('Split', 'Stockholm'), ('Munich', 'Amsterdam'),
        ('Split', 'Amsterdam'), ('Amsterdam', 'Stockholm'), ('Amsterdam', 'Riga'),
        ('Vienna', 'Stockholm'), ('Vienna', 'Istanbul'), ('Vienna', 'Seville'),
        ('Istanbul', 'Amsterdam'), ('Munich', 'Brussels'), ('Prague', 'Munich'),
        ('Riga', 'Munich'), ('Prague', 'Amsterdam'), ('Prague', 'Brussels'),
        ('Prague', 'Istanbul'), ('Istanbul', 'Stockholm'), ('Vienna', 'Prague'),
        ('Munich', 'Split'), ('Vienna', 'Amsterdam'), ('Prague', 'Stockholm'),
        ('Brussels', 'Seville'), ('Munich', 'Stockholm'), ('Istanbul', 'Brussels'),
        ('Amsterdam', 'Seville'), ('Vienna', 'Split'), ('Munich', 'Seville'),
        ('Riga', 'Brussels'), ('Prague', 'Riga'), ('Vienna', 'Munich')
    ]

    # Create adjacency list
    direct_flights = {city: set() for city in cities}
    for a, b in flight_pairs:
        direct_flights[a].add(b)
        direct_flights[b].add(a)

    # Days are 1..20
    days = 20
    city_vars = [Int(f'day_{i}_city') for i in range(1, days + 1)]
    s = Solver()

    # Each day's city must be a valid city index
    for day in range(days):
        s.add(city_vars[day] >= 0, city_vars[day] < len(cities))

    # Flight constraints between consecutive days
    for day in range(days - 1):
        current = city_vars[day]
        next_city = city_vars[day + 1]
        # Either stay or fly to connected city
        constraints = [current == next_city]
        for c1 in direct_flights:
            for c2 in direct_flights[c1]:
                constraints.append(And(current == city_to_idx[c1], 
                                    next_city == city_to_idx[c2]))
        s.add(Or(*constraints))

    # Fixed constraints:
    # 1. 5 days in Prague including days 5-9
    s.add(Or(
        *[And(*[city_vars[d] == city_to_idx['Prague'] for d in range(start, start + 5)])
        for start in range(5) if start + 5 <= days
    ))

    # 2. 2 days in Brussels
    s.add(Sum([If(city_vars[i] == city_to_idx['Brussels'], 1, 0) for i in range(days)]) == 2)

    # 3. 2 days in Riga including day 15 or 16
    s.add(Sum([If(city_vars[i] == city_to_idx['Riga'], 1, 0) for i in range(days)]) == 2)
    s.add(Or(city_vars[14] == city_to_idx['Riga'], city_vars[15] == city_to_idx['Riga']))

    # 4. 2 days in Munich
    s.add(Sum([If(city_vars[i] == city_to_idx['Munich'], 1, 0) for i in range(days)]) == 2)

    # 5. 3 days in Seville
    s.add(Sum([If(city_vars[i] == city_to_idx['Seville'], 1, 0) for i in range(days)]) == 3)

    # 6. 2 days in Stockholm including conference on days 16-17
    s.add(Sum([If(city_vars[i] == city_to_idx['Stockholm'], 1, 0) for i in range(days)]) == 2)
    s.add(Or(city_vars[15] == city_to_idx['Stockholm'], city_vars[16] == city_to_idx['Stockholm']))

    # 7. 2 days in Istanbul
    s.add(Sum([If(city_vars[i] == city_to_idx['Istanbul'], 1, 0) for i in range(days)]) == 2)

    # 8. 3 days in Amsterdam
    s.add(Sum([If(city_vars[i] == city_to_idx['Amsterdam'], 1, 0) for i in range(days)]) == 3)

    # 9. 5 days in Vienna including days 1-5
    s.add(Sum([If(city_vars[i] == city_to_idx['Vienna'], 1, 0) for i in range(days)]) == 5)
    s.add(Or(*[city_vars[i] == city_to_idx['Vienna'] for i in range(5)]))

    # 10. 3 days in Split including days 11-13
    s.add(Sum([If(city_vars[i] == city_to_idx['Split'], 1, 0) for i in range(days)]) == 3)
    s.add(Or(*[city_vars[i] == city_to_idx['Split'] for i in range(10, 13)]))

    # Solve and generate itinerary
    if s.check() == sat:
        model = s.model()
        sequence = []
        for day in range(days):
            city_idx = model.evaluate(city_vars[day]).as_long()
            sequence.append(idx_to_city[city_idx])

        itinerary = []
        current_place = sequence[0]
        start_day = 1
        for day in range(1, days):
            if sequence[day] != current_place:
                end_day = day
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {end_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {end_day}", "place": sequence[day]})
                start_day = day + 1
                current_place = sequence[day]
        itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found."}

# Execute and print result
result = solve_itinerary()
print(json.dumps(result, indent=2))