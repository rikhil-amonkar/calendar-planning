from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Berlin": 5,
        "Split": 3,
        "Bucharest": 3,
        "Riga": 5,
        "Lisbon": 3,
        "Tallinn": 4,
        "Lyon": 5
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Lisbon", "Bucharest"),
        ("Berlin", "Lisbon"),
        ("Bucharest", "Riga"),
        ("Berlin", "Riga"),
        ("Split", "Lyon"),
        ("Lisbon", "Riga"),
        ("Riga", "Tallinn"),
        ("Berlin", "Split"),
        ("Lyon", "Lisbon"),
        ("Berlin", "Tallinn"),
        ("Lyon", "Bucharest")
    ]
    
    # Make flight connections bidirectional
    flight_connections = {}
    for city in cities:
        flight_connections[city] = []
    for a, b in direct_flights:
        flight_connections[a].append(b)
        flight_connections[b].append(a)
    
    total_days = 22
    days = range(1, total_days + 1)
    
    # Create Z3 variables: for each day, which city is visited
    day_city = {day: Int(f"day_{day}") for day in days}
    
    s = Solver()
    
    # Assign each day to a city code (we'll map cities to integers)
    city_to_int = {city: idx for idx, city in enumerate(cities.keys())}
    int_to_city = {idx: city for city, idx in city_to_int.items()}
    
    for day in days:
        s.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Constraint: Berlin from day 1 to 5
    for day in range(1, 6):
        s.add(day_city[day] == city_to_int["Berlin"])
    
    # Constraint: Lyon between day 7 and 11 (wedding)
    # The 5-day Lyon stay must be contiguous within 7-11.
    # So possible start days: 7 (7+5-1=11)
    for day in range(7, 12):
        s.add(day_city[day] == city_to_int["Lyon"])
    
    # Constraint: Bucharest between day 13 and 15 (3 days)
    for day in range(13, 16):
        s.add(day_city[day] == city_to_int["Bucharest"])
    
    # Constraint: Total days per city
    for city, req_days in cities.items():
        total = 0
        for day in days:
            total += If(day_city[day] == city_to_int[city], 1, 0)
        s.add(total == req_days)
    
    # Constraint: Flight transitions are only between connected cities
    for day in range(1, total_days):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # Either stay in the same city or move to a connected city
        same_city = current_city == next_city
        connected = Or([And(current_city == city_to_int[a], next_city == city_to_int[b]) 
                      for a in cities for b in flight_connections[a]])
        s.add(Or(same_city, connected))
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        # Extract the day-city sequence
        day_sequence = []
        for day in days:
            city_idx = m.evaluate(day_city[day]).as_long()
            city = int_to_city[city_idx]
            day_sequence.append((day, city))
        
        # Generate the itinerary
        itinerary = []
        i = 0
        n = len(day_sequence)
        while i < n:
            current_day, current_city = day_sequence[i]
            start_day = current_day
            # Find the end of the current stay
            while i < n and day_sequence[i][1] == current_city:
                i += 1
            end_day = day_sequence[i - 1][0]
            
            # Add the stay entry
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
            
            # If there's a next city, add the flight day entries
            if i < n:
                next_day, next_city = day_sequence[i]
                # The flight is on end_day (departure) and next_day (arrival)
                # But since end_day is the last day in current_city, and next_day is the first in next_city,
                # and the flight happens on the same day, we need to represent both cities on that day
                itinerary.append({"day_range": f"Day {end_day}", "place": current_city})
                itinerary.append({"day_range": f"Day {next_day}", "place": next_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))