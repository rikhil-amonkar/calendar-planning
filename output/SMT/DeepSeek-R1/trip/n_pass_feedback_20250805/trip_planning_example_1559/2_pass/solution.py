from z3 import *
import json

def main():
    # Define city names and their indices
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
    city_days = [2, 3, 4, 3, 4, 4, 5, 2, 5, 2]
    
    # Mapping of city names to indices
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    # Define the direct flights as a set of tuples (min_index, max_index)
    flight_strings = [
        "Lisbon and Paris", "Lyon and Nice", "Tallinn and Oslo", "Prague and Lyon",
        "Paris and Oslo", "Lisbon and Seville", "Prague and Lisbon", "Oslo and Nice",
        "Valencia and Paris", "Valencia and Lisbon", "Paris and Nice", "Nice and Mykonos",
        "Paris and Lyon", "Valencia and Lyon", "Prague and Oslo", "Prague and Paris",
        "Seville and Paris", "Oslo and Lyon", "Prague and Valencia", "Lisbon and Nice",
        "Lisbon and Oslo", "Valencia and Seville", "Lisbon and Lyon", "Paris and Tallinn",
        "Prague and Tallinn"
    ]
    
    allowed_edges = set()
    for flight in flight_strings:
        parts = flight.split(" and ")
        idx1 = city_to_index[parts[0]]
        idx2 = city_to_index[parts[1]]
        edge = (min(idx1, idx2), max(idx1, idx2))
        allowed_edges.add(edge)
    
    # Create directed edges for both directions
    directed_edges = set()
    for (u, v) in allowed_edges:
        directed_edges.add((u, v))
        directed_edges.add((v, u))
    
    # Initialize Z3 solver and variables
    s = Solver()
    
    # order[i] is the city index at position i in the sequence
    order = [Int(f"order_{i}") for i in range(10)]
    # s_pos[i] is the start day for the city at position i
    s_pos = [Int(f"s_pos_{i}") for i in range(10)]
    # start_day[j] is the start day for city j
    start_day = [Int(f"start_day_{j}") for j in range(10)]
    
    # Create an array for city days
    days_arr = Array('days_arr', IntSort(), IntSort())
    for j in range(10):
        s.add(days_arr[j] == city_days[j])
    
    # Constraints: order is a permutation of 0 to 9
    s.add([And(0 <= order[i], order[i] < 10) for i in range(10)])
    s.add(Distinct(order))
    
    # Start day of the first city is 1
    s.add(s_pos[0] == 1)
    
    # Constraints for s_pos: s_pos[i] = s_pos[i-1] + (days_arr[order[i-1]] - 1)
    for i in range(1, 10):
        prev_city = order[i-1]
        s.add(s_pos[i] == s_pos[i-1] + Select(days_arr, prev_city) - 1)
    
    # Constraints for start_day: for each city j, start_day[j] = s_pos[i] for the i where order[i] == j
    for j in range(10):
        s.add(Or([And(order[i] == j, start_day[j] == s_pos[i]) for i in range(10)]))
    
    # Event constraints
    # Valencia (index 0): start_day in [2,4] (ensures days 3 or 4 are included)
    s.add(And(start_day[0] >= 2, start_day[0] <= 4))
    # Oslo (index 1): start_day in [11,15] (ensures days 13-15 are included)
    s.add(And(start_day[1] >= 11, start_day[1] <= 15))
    # Seville (index 6): start_day <= 9 (ensures at least one day between 5-9)
    s.add(start_day[6] <= 9)
    # Mykonos (index 8): start_day in [17,21] (ensures days 21-25 are included)
    s.add(And(start_day[8] >= 17, start_day[8] <= 21))
    
    # Flight constraints: consecutive cities in the sequence must have a direct flight
    for i in range(9):
        a = order[i]
        b = order[i+1]
        s.add(Or([And(a == u, b == v) for (u, v) in directed_edges]))
    
    # Ensure the trip ends on day 25
    last_day = s_pos[9] + Select(days_arr, order[9]) - 1
    s.add(last_day == 25)
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Retrieve start days for each city
        start_day_vals = []
        for j in range(10):
            val = model.evaluate(start_day[j])
            start_day_vals.append(val.as_long() if is_int_value(val) else val)
        
        # Generate itinerary
        itinerary = []
        for j in range(10):
            city_name = cities[j]
            start = start_day_vals[j]
            end = start + city_days[j] - 1
            for day in range(start, end + 1):
                itinerary.append({"day": day, "city": city_name})
        
        # Sort itinerary by day
        itinerary_sorted = sorted(itinerary, key=lambda x: x['day'])
        
        # Output as JSON
        result = {'itinerary': itinerary_sorted}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()