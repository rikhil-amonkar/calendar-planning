from z3 import *

def main():
    # Create the solver
    s = Solver()

    # City indices
    cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
    city_idx = {city: i for i, city in enumerate(cities)}
    n_cities = len(cities)
    n_segments = 7  # 7 segments for 7 cities
    total_days = 15

    # Segment variables: start and end days for each segment
    starts = [Int(f"start_{i}") for i in range(n_segments)]
    ends = [Int(f"end_{i}") for i in range(n_segments)]
    city_vars = [Int(f"city_{i}") for i in range(n_segments)]  # city index for each segment

    # Each segment's city is one of the 7 cities
    for i in range(n_segments):
        s.add(And(city_vars[i] >= 0, city_vars[i] < n_cities))

    # First segment starts on day 1
    s.add(starts[0] == 1)
    # Last segment ends on day 15
    s.add(ends[n_segments - 1] == total_days)
    # For consecutive segments, the next start is the same as the current end (flight day)
    for i in range(n_segments - 1):
        s.add(starts[i+1] == ends[i])
    # End day must be at least start day
    for i in range(n_segments):
        s.add(ends[i] >= starts[i])

    # Direct flight connections between consecutive segments
    direct_flights = [
        ("London", "Amsterdam"),
        ("Vilnius", "Frankfurt"),
        ("Riga", "Vilnius"),
        ("Riga", "Stockholm"),
        ("London", "Bucharest"),
        ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Frankfurt"),
        ("Frankfurt", "Stockholm"),
        ("Bucharest", "Riga"),
        ("Amsterdam", "Riga"),
        ("Amsterdam", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Bucharest", "Frankfurt"),
        ("London", "Frankfurt"),
        ("London", "Stockholm"),
        ("Amsterdam", "Vilnius")
    ]
    # Convert to city indices
    flight_pairs = []
    for a, b in direct_flights:
        flight_pairs.append((city_idx[a], city_idx[b]))
        flight_pairs.append((city_idx[b], city_idx[a]))
    
    for i in range(n_segments - 1):
        c1 = city_vars[i]
        c2 = city_vars[i+1]
        s.add(Or([And(c1 == a, c2 == b) for a, b in flight_pairs]))

    # Total days per city
    total_days_per_city = [0] * n_cities
    for c in range(n_cities):
        total_days_per_city[c] = sum(If(city_vars[i] == c, ends[i] - starts[i] + 1, 0) for i in range(n_segments))
    s.add(total_days_per_city[city_idx["Riga"]] == 2)
    s.add(total_days_per_city[city_idx["Frankfurt"]] == 3)
    s.add(total_days_per_city[city_idx["Amsterdam"]] == 2)
    s.add(total_days_per_city[city_idx["Vilnius"]] == 5)
    s.add(total_days_per_city[city_idx["London"]] == 2)
    s.add(total_days_per_city[city_idx["Stockholm"]] == 3)
    s.add(total_days_per_city[city_idx["Bucharest"]] == 4)

    # Event constraints: Vilnius must include at least one day between 7 and 11, similarly for Stockholm and Amsterdam.
    # For Vilnius: there must be a segment where the city is Vilnius and the segment overlaps [7, 11]
    vilnius_segment = Or([And(city_vars[i] == city_idx["Vilnius"], starts[i] <= 11, ends[i] >= 7) for i in range(n_segments)])
    s.add(vilnius_segment)
    # For Stockholm: overlaps [13, 15]
    stockholm_segment = Or([And(city_vars[i] == city_idx["Stockholm"], starts[i] <= 15, ends[i] >= 13) for i in range(n_segments)])
    s.add(stockholm_segment)
    # For Amsterdam: at least one day between 2 and 3
    amsterdam_segment = Or([And(city_vars[i] == city_idx["Amsterdam"], starts[i] <= 3, ends[i] >= 2) for i in range(n_segments)])
    s.add(amsterdam_segment)

    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Extract the itinerary
        itinerary = []
        for i in range(n_segments):
            start_val = model[starts[i]].as_long()
            end_val = model[ends[i]].as_long()
            city_val = model[city_vars[i]].as_long()
            city_name = cities[city_val]
            # Add the continuous stay
            itinerary.append({"day_range": f"Day {start_val}-{end_val}", "place": city_name})
            # If this is not the first segment, then the start day is also the end day of the previous segment (flight day)
            if i > 0:
                # Add the flight day for the departure from the previous city
                prev_city = cities[model[city_vars[i-1]].as_long()]
                itinerary.append({"day_range": f"Day {start_val}", "place": prev_city})
                # Add the flight day for the arrival to the current city
                itinerary.append({"day_range": f"Day {start_val}", "place": city_name})
            # For the last day of the segment, if it is not the last segment, then we will handle the flight in the next segment
            # For the last segment, no flight after
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()