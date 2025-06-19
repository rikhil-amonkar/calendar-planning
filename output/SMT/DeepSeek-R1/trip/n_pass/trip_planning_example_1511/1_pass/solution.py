from z3 import *
import json

def main():
    cities = ["Venice", "Reykjavik", "Munich", "Santorini", "Manchester", "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"]
    n_cities = len(cities)
    n_days = 24

    edges = [
        ("Bucharest", "Manchester"), 
        ("Munich", "Venice"), 
        ("Santorini", "Manchester"), 
        ("Vienna", "Reykjavik"), 
        ("Venice", "Santorini"), 
        ("Munich", "Porto"), 
        ("Valencia", "Vienna"), 
        ("Manchester", "Vienna"), 
        ("Porto", "Vienna"), 
        ("Venice", "Manchester"), 
        ("Santorini", "Vienna"), 
        ("Munich", "Manchester"), 
        ("Munich", "Reykjavik"), 
        ("Bucharest", "Valencia"), 
        ("Venice", "Vienna"), 
        ("Bucharest", "Vienna"), 
        ("Porto", "Manchester"), 
        ("Munich", "Vienna"), 
        ("Valencia", "Porto"), 
        ("Munich", "Bucharest"), 
        ("Tallinn", "Munich"), 
        ("Santorini", "Bucharest"), 
        ("Munich", "Valencia")
    ]

    city_to_index = {city: idx for idx, city in enumerate(cities)}
    directed_flights_set = set()
    for (a, b) in edges:
        a_fixed = "Munich" if a == "Munich" else a
        b_fixed = "Munich" if b == "Munich" else b
        a_fixed = "Venice" if a == "Venice" else a_fixed
        b_fixed = "Venice" if b == "Venice" else b_fixed
        a_fixed = "Vienna" if a == "Vienna" else a_fixed
        b_fixed = "Vienna" if b == "Vienna" else b_fixed
        if a_fixed in city_to_index and b_fixed in city_to_index:
            i1 = city_to_index[a_fixed]
            i2 = city_to_index[b_fixed]
            directed_flights_set.add((i1, i2))
            directed_flights_set.add((i2, i1))

    s = Solver()

    city_start = [Int(f'city_start_{i}') for i in range(n_days)]
    flight = [Bool(f'flight_{i}') for i in range(n_days-1)]
    dest = [Int(f'dest_{i}') for i in range(n_days-1)]

    for i in range(n_days):
        s.add(city_start[i] >= 0, city_start[i] < n_cities)
    for i in range(n_days-1):
        s.add(dest[i] >= 0, dest[i] < n_cities)

    for i in range(n_days-1):
        flight_condition = And(
            city_start[i+1] == dest[i],
            Or([And(city_start[i] == a, dest[i] == b) for (a, b) in directed_flights_set])
        )
        s.add(If(flight[i], flight_condition, city_start[i+1] == city_start[i]))

    munich_index = city_to_index["Munich"]
    s.add(city_start[3] == munich_index)
    s.add(Not(flight[3]))
    s.add(Not(flight[4]))
    s.add(Not(flight[5]))

    santorini_index = city_to_index["Santorini"]
    conds_santorini = []
    for d in [7, 8, 9]:
        cond = Or(city_start[d] == santorini_index, And(flight[d], dest[d] == santorini_index))
        conds_santorini.append(cond)
    s.add(Or(conds_santorini))

    valencia_index = city_to_index["Valencia"]
    conds_valencia = []
    for d in [13, 14]:
        cond = Or(city_start[d] == valencia_index, And(flight[d], dest[d] == valencia_index))
        conds_valencia.append(cond)
    s.add(Or(conds_valencia))

    required_days = [
        3,  # Venice
        2,  # Reykjavik
        3,  # Munich
        3,  # Santorini
        3,  # Manchester
        3,  # Porto
        5,  # Bucharest
        4,  # Tallinn
        2,  # Valencia
        5   # Vienna
    ]
    for c in range(n_cities):
        total = 0
        for i in range(n_days-1):
            in_city = Or(city_start[i] == c, And(flight[i], dest[i] == c))
            total += If(in_city, 1, 0)
        total += If(city_start[n_days-1] == c, 1, 0)
        s.add(total == required_days[c])

    if s.check() == sat:
        m = s.model()
        city_start_val = [m.evaluate(city_start[i]).as_long() for i in range(n_days)]
        flight_val = [is_true(m.evaluate(flight[i])) for i in range(n_days-1)]
        dest_val = [m.evaluate(dest[i]).as_long() for i in range(n_days-1)]

        stays = []
        flights = []
        current_city = city_start_val[0]
        start_day = 1
        for i in range(n_days-1):
            if flight_val[i]:
                end_day = i+1
                stays.append((start_day, end_day, current_city))
                flights.append((i+1, current_city, dest_val[i]))
                current_city = dest_val[i]
                start_day = i+1
        stays.append((start_day, n_days, current_city))

        itinerary = []
        for (s, e, c) in stays:
            if s == e:
                itinerary.append({"day_range": f"Day {s}", "place": cities[c], "type": "stay"})
            else:
                itinerary.append({"day_range": f"Day {s}-{e}", "place": cities[c], "type": "stay"})
        for (d, from_c, to_c) in flights:
            itinerary.append({"day_range": f"Day {d}", "place": cities[from_c], "type": "flight"})
            itinerary.append({"day_range": f"Day {d}", "place": cities[to_c], "type": "flight"})

        def get_start_day(record):
            s = record['day_range']
            if s.startswith('Day '):
                parts = s[4:].split('-')
                return int(parts[0])
            return 0

        itinerary.sort(key=lambda r: (get_start_day(r), 0 if r['type'] == 'flight' else 1))
        for record in itinerary:
            del record['type']

        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()