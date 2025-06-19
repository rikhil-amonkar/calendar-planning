from z3 import *

def main():
    # Define city constants
    manchester = 0
    madrid = 1
    stuttgart = 2
    vienna = 3
    city_names = {
        manchester: "Manchester",
        madrid: "Madrid",
        stuttgart: "Stuttgart",
        vienna: "Vienna"
    }
    
    # Allowed directed flights (both directions)
    allowed_directed = [
        (manchester, madrid),
        (madrid, manchester),
        (manchester, stuttgart),
        (stuttgart, manchester),
        (manchester, vienna),
        (vienna, manchester),
        (madrid, vienna),
        (vienna, madrid),
        (stuttgart, vienna),
        (vienna, stuttgart)
    ]
    
    # Create Z3 variables for 15 days
    n_days = 15
    city_start = [Int(f'city_start_{i}') for i in range(n_days)]
    city_end = [Int(f'city_end_{i}') for i in range(n_days)]
    
    s = Solver()
    
    # Constraint: cities must be in {0,1,2,3}
    for i in range(n_days):
        s.add(And(city_start[i] >= 0, city_start[i] <= 3))
        s.add(And(city_end[i] >= 0, city_end[i] <= 3))
    
    # Continuity constraint: city_end[i] must equal city_start[i+1] for i from 0 to 13
    for i in range(n_days - 1):
        s.add(city_end[i] == city_start[i+1])
    
    # Flight constraints: for each day, either no flight (start == end) or flight in allowed_directed
    for i in range(n_days):
        no_flight = (city_start[i] == city_end[i])
        flight_conds = []
        for (a, b) in allowed_directed:
            flight_conds.append(And(city_start[i] == a, city_end[i] == b))
        flight_cond = Or(flight_conds)
        s.add(Or(no_flight, flight_cond))
    
    # Function to count days in a city
    def count_days(c):
        total = 0
        for i in range(n_days):
            # Count the start day
            total += If(city_start[i] == c, 1, 0)
            # Count the end day if it's a flight and the end is c and start is not c
            total += If(And(city_end[i] == c, city_start[i] != c), 1, 0)
        return total
    
    s.add(count_days(manchester) == 7)
    s.add(count_days(madrid) == 4)
    s.add(count_days(stuttgart) == 5)
    s.add(count_days(vienna) == 2)
    
    # Event constraints
    # Manchester: at least one day in [1,7] (indices 0 to 6)
    manchester_event = []
    for i in range(0, 7):  # days 1 to 7
        cond = Or(
            city_start[i] == manchester,
            And(city_end[i] == manchester, city_start[i] != manchester)
        )
        manchester_event.append(cond)
    s.add(Or(manchester_event))
    
    # Stuttgart: at least one day in [11,15] (indices 10 to 14)
    stuttgart_event = []
    for i in range(10, 15):  # days 11 to 15
        cond = Or(
            city_start[i] == stuttgart,
            And(city_end[i] == stuttgart, city_start[i] != stuttgart)
        )
        stuttgart_event.append(cond)
    s.add(Or(stuttgart_event))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        start_vals = [m.eval(city_start[i]).as_long() for i in range(n_days)]
        end_vals = [m.eval(city_end[i]).as_long() for i in range(n_days)]
        
        # Generate contiguous blocks
        blocks = []  # (start_day, end_day, city_index)
        current_start_idx = 0
        current_city = start_vals[0]
        for i in range(n_days):
            if start_vals[i] != end_vals[i]:  # flight on day i+1
                # End the current block: from current_start_idx+1 to i+1
                blocks.append((current_start_idx + 1, i + 1, current_city))
                # The next block starts at day i+1 (same day) for the arrival city
                current_city = end_vals[i]
                current_start_idx = i
        # Add the last block
        blocks.append((current_start_idx + 1, n_days, current_city))
        
        # Generate flight days
        flight_days = []  # (day, dep_city, arr_city)
        for i in range(n_days):
            if start_vals[i] != end_vals[i]:
                flight_days.append((i + 1, start_vals[i], end_vals[i]))
        
        # Format itinerary
        itinerary = []
        # Add block records
        for (start, end, c) in blocks:
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({
                "day_range": day_range_str,
                "place": city_names[c]
            })
        # Add flight day records
        for (day, dep, arr) in flight_days:
            itinerary.append({
                "day_range": f"Day {day}",
                "place": city_names[dep]
            })
            itinerary.append({
                "day_range": f"Day {day}",
                "place": city_names[arr]
            })
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()