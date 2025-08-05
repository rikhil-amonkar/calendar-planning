from z3 import *

def main():
    city_to_index = {
        "Krakow": 0,
        "Frankfurt": 1,
        "Oslo": 2,
        "Dubrovnik": 3,
        "Naples": 4
    }
    index_to_city = {v: k for k, v in city_to_index.items()}
    durations = {
        0: 5,  # Krakow
        1: 4,  # Frankfurt
        2: 3,  # Oslo
        3: 5,  # Dubrovnik
        4: 5   # Naples
    }

    # Define direct flight connections as undirected pairs
    direct_flights = [
        ("Dubrovnik", "Oslo"),
        ("Frankfurt", "Krakow"),
        ("Frankfurt", "Oslo"),
        ("Dubrovnik", "Frankfurt"),
        ("Krakow", "Oslo"),
        ("Naples", "Oslo"),
        ("Naples", "Dubrovnik"),
        ("Naples", "Frankfurt")
    ]
    allowed_pairs = set()
    for a, b in direct_flights:
        idx_a = city_to_index[a]
        idx_b = city_to_index[b]
        pair = (min(idx_a, idx_b), max(idx_a, idx_b))
        allowed_pairs.add(pair)

    s = Solver()

    # Order of city visits (5 cities)
    order = [Int(f'order_{i}') for i in range(5)]
    for i in range(5):
        s.add(order[i] >= 0, order[i] < 5)  # Cities indexed 0 to 4
    s.add(Distinct(order))  # Each city visited exactly once

    # Start and end days for each segment
    starts = [Int(f'start_{i}') for i in range(5)]
    ends = [Int(f'end_{i}') for i in range(5)]

    # First segment starts on day 1
    s.add(starts[0] == 1)
    # Segments are contiguous: next starts after current ends
    for i in range(4):
        s.add(starts[i+1] == ends[i] + 1)
    # Total trip ends on day 18
    s.add(ends[4] == 18)

    # Set segment durations based on city using Z3 expressions
    for i in range(5):
        city_idx = order[i]
        # Use Z3 If expressions to get duration based on city index
        duration = If(city_idx == 0, durations[0],
                 If(city_idx == 1, durations[1],
                 If(city_idx == 2, durations[2],
                 If(city_idx == 3, durations[3], 
                                 durations[4]))))
        s.add(ends[i] == starts[i] + duration - 1)

    # Event in Dubrovnik between days 5 and 9 inclusive: must overlap
    for i in range(5):
        city_idx = order[i]
        # If this segment is Dubrovnik, ensure overlap with [5,9]
        s.add(If(city_idx == city_to_index["Dubrovnik"],
                 And(starts[i] <= 9, ends[i] >= 5),
                 True))
        # Event in Oslo between days 16 and 18 inclusive: must overlap
        s.add(If(city_idx == city_to_index["Oslo"],
                 And(starts[i] <= 18, ends[i] >= 16),
                 True))

    # Flight connections: consecutive cities must have a direct flight
    for i in range(4):
        city1 = order[i]
        city2 = order[i+1]
        # Consider both orders for the flight pair
        low = If(city1 < city2, city1, city2)
        high = If(city1 < city2, city2, city1)
        # Build a list of conditions for each allowed pair
        flight_conditions = []
        for pair in allowed_pairs:
            cond = And(low == pair[0], high == pair[1])
            flight_conditions.append(cond)
        # Require at least one valid flight connection
        s.add(Or(flight_conditions))

    # Exclude the previous invalid itinerary: Krakow -> Frankfurt -> Dubrovnik -> Naples -> Oslo
    s.add(Not(And(
        order[0] == city_to_index["Krakow"],
        order[1] == city_to_index["Frankfurt"],
        order[2] == city_to_index["Dubrovnik"],
        order[3] == city_to_index["Naples"],
        order[4] == city_to_index["Oslo"]
    )))

    if s.check() == sat:
        model = s.model()
        order_vals = [model.evaluate(order[i]).as_long() for i in range(5)]
        start_vals = [model.evaluate(starts[i]).as_long() for i in range(5)]
        end_vals = [model.evaluate(ends[i]).as_long() for i in range(5)]
        
        itinerary = []
        for i in range(5):
            city_idx = order_vals[i]
            city_name = index_to_city[city_idx]
            start_day = start_vals[i]
            end_day = end_vals[i]
            itinerary.append({
                'day_range': f'Day {start_day}-{end_day}',
                'place': city_name
            })
        
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()