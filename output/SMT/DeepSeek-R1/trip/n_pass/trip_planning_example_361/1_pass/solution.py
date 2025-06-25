from z3 import *

def main():
    n_days = 15
    cities = {0: "Madrid", 1: "Paris", 2: "Bucharest", 3: "Seville"}
    allowed_edges = [(0,1), (1,0), (0,2), (2,0), (0,3), (3,0), (1,2), (2,1), (1,3), (3,1)]
    
    # Create Z3 variables
    start_city = [Int(f'start_city_{i+1}') for i in range(n_days)]
    flight_day = [Bool(f'flight_day_{i+1}') for i in range(n_days)]
    flight_to = [Int(f'flight_to_{i+1}') for i in range(n_days)]
    
    s = Solver()
    
    # Each start_city must be in [0,3]
    for i in range(n_days):
        s.add(And(start_city[i] >= 0, start_city[i] <= 3))
    
    # Each flight_to must be in [0,3] if flight_day is True
    for i in range(n_days):
        s.add(Implies(flight_day[i], And(flight_to[i] >= 0, flight_to[i] <= 3)))
    
    # No flight on day 15
    s.add(Not(flight_day[14]))
    
    # Start in Madrid on day 1
    s.add(start_city[0] == 0)
    
    # Constraints for days 1 to 14
    for i in range(0, n_days-1):
        s.add(If(flight_day[i],
                 And(start_city[i+1] == flight_to[i],
                     Or([And(start_city[i] == a, flight_to[i] == b) for (a,b) in allowed_edges])
                 ),
                 start_city[i+1] == start_city[i]
        ))
    
    # Must be in Madrid on days 1-7
    for i in range(0, 7):  # days 1 to 7
        s.add(Or(start_city[i] == 0, And(flight_day[i], flight_to[i] == 0)))
    
    # Must be in Bucharest on day 14 and day 15
    s.add(Or(start_city[13] == 2, And(flight_day[13], flight_to[13] == 2)))  # day 14
    s.add(start_city[14] == 2)  # day 15
    
    # Count days in each city
    madrid_days = 0
    paris_days = 0
    bucharest_days = 0
    seville_days = 0
    
    for i in range(0, n_days):
        # Count start_city
        madrid_days += If(start_city[i] == 0, 1, 0)
        paris_days += If(start_city[i] == 1, 1, 0)
        bucharest_days += If(start_city[i] == 2, 1, 0)
        seville_days += If(start_city[i] == 3, 1, 0)
        
        # Count flight_to if flight_day is True
        madrid_days += If(And(flight_day[i], flight_to[i] == 0), 1, 0)
        paris_days += If(And(flight_day[i], flight_to[i] == 1), 1, 0)
        bucharest_days += If(And(flight_day[i], flight_to[i] == 2), 1, 0)
        seville_days += If(And(flight_day[i], flight_to[i] == 3), 1, 0)
    
    s.add(madrid_days == 7)
    s.add(paris_days == 6)
    s.add(bucharest_days == 2)
    s.add(seville_days == 3)
    
    # Exactly 3 flight days (days 1 to 14)
    flight_days = Sum([If(flight_day[i], 1, 0) for i in range(0, 14)])
    s.add(flight_days == 3)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        
        # Extract values
        start_city_vals = [m.evaluate(start_city[i]).as_long() for i in range(n_days)]
        flight_day_vals = [m.evaluate(flight_day[i]) for i in range(n_days)]
        flight_to_vals = [m.evaluate(flight_to[i]).as_long() if flight_day_vals[i] else -1 for i in range(n_days)]
        
        # Build blocks and flights
        blocks = []
        flights = []
        current_start = 1
        current_city = start_city_vals[0]
        
        for i in range(0, n_days):
            if i < n_days - 1 and flight_day_vals[i]:
                end_day = i+1
                blocks.append((current_start, end_day, current_city))
                flights.append((end_day, current_city, flight_to_vals[i]))
                current_city = flight_to_vals[i]
                current_start = end_day
        blocks.append((current_start, n_days, current_city))
        
        # Build itinerary
        itinerary_list = []
        for idx, (s_day, e_day, city_idx) in enumerate(blocks):
            if s_day == e_day:
                day_range_str = f"Day {s_day}"
            else:
                day_range_str = f"Day {s_day}-{e_day}"
            itinerary_list.append({"day_range": day_range_str, "place": cities[city_idx]})
            if idx < len(flights):
                d, from_c, to_c = flights[idx]
                itinerary_list.append({"day_range": f"Day {d}", "place": cities[from_c]})
                itinerary_list.append({"day_range": f"Day {d}", "place": cities[to_c]})
        
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()