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
    # The wedding is a continuous block of 5 days within 7-11
    # So possible start days for Lyon wedding: 7,8 (since 7+5-1=11)
    # We'll say that at least 5 consecutive days within 7-11 are Lyon.
    # But since Lyon total is 5, the wedding is the entire Lyon stay.
    # So the 5-day Lyon stay must be contiguous within 7-11.
    lyon_possible_starts = [7, 8]  # because 7+5-1=11, 8+5-1=12 (but 12>11, so only 7)
    # So the only possible start is 7.
    s.add(day_city[7] == city_to_int["Lyon"])
    s.add(day_city[8] == city_to_int["Lyon"])
    s.add(day_city[9] == city_to_int["Lyon"])
    s.add(day_city[10] == city_to_int["Lyon"])
    s.add(day_city[11] == city_to_int["Lyon"])
    
    # Constraint: Bucharest between day 13 and 15 (3 days)
    # So possible start days: 13 (13+3-1=15)
    s.add(day_city[13] == city_to_int["Bucharest"])
    s.add(day_city[14] == city_to_int["Bucharest"])
    s.add(day_city[15] == city_to_int["Bucharest"])
    
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
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_int[a], next_city == city_to_int[b]) 
              for a in cities for b in flight_connections[a] if city_to_int[b] > city_to_int[a]]  # to avoid duplicates
        ))
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        # Extract the itinerary
        itinerary = []
        current_stay_start = 1
        current_city = int_to_city[m.evaluate(day_city[1]).as_long()]
        
        for day in range(1, total_days + 1):
            city_idx = m.evaluate(day_city[day]).as_long()
            city = int_to_city[city_idx]
            if day == 1:
                continue  # handled after loop
            
            prev_city_idx = m.evaluate(day_city[day - 1]).as_long()
            prev_city = int_to_city[prev_city_idx]
            
            if prev_city != city:
                # Flight day: day-1 is the departure day, day is arrival
                # Add the departure part
                if current_stay_start <= day - 1:
                    if current_stay_start == day - 1:
                        itinerary.append({"day_range": f"Day {day-1}", "place": prev_city})
                    else:
                        itinerary.append({"day_range": f"Day {current_stay_start}-{day-1}", "place": prev_city})
                        itinerary.append({"day_range": f"Day {day-1}", "place": prev_city})
                # Add the arrival part
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_stay_start = day
                current_city = city
            # else: continue the stay
        
        # Add the last stay
        if current_stay_start <= total_days:
            if current_stay_start == total_days:
                itinerary.append({"day_range": f"Day {total_days}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {current_stay_start}-{total_days}", "place": current_city})
        
        # Now, post-process to handle flight days correctly (days with both departure and arrival)
        # Reconstruct the itinerary more carefully
        day_places = []
        for day in days:
            city_idx = m.evaluate(day_city[day]).as_long()
            city = int_to_city[city_idx]
            day_places.append((day, city))
        
        new_itinerary = []
        i = 0
        while i < len(day_places):
            day, city = day_places[i]
            start_day = day
            # Check if next day is the same city
            while i + 1 < len(day_places) and day_places[i+1][1] == city:
                i += 1
                day = day_places[i][0]
            end_day = day
            if start_day == end_day:
                new_itinerary.append({"day_range": f"Day {start_day}", "place": city})
            else:
                new_itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
            i += 1
        
        # Now, handle flight days: when consecutive days are different cities, insert the flight day records
        final_itinerary = []
        for i in range(len(new_itinerary)):
            entry = new_itinerary[i]
            final_itinerary.append(entry)
            if i < len(new_itinerary) - 1:
                next_entry = new_itinerary[i + 1]
                current_day_range = entry["day_range"]
                next_day_range = next_entry["day_range"]
                # Parse current end day and next start day
                current_end = int(current_day_range.split('-')[-1].replace('Day ', ''))
                next_start = int(next_day_range.split('-')[0].replace('Day ', ''))
                if next_start == current_end + 1:
                    # Flight between current_end and next_start
                    # The flight is on current_end (departure) and next_start (arrival)
                    # So we need to duplicate the current_end as departure and next_start as arrival
                    pass  # handled by the day ranges
                elif next_start == current_end:
                    # Flight on the same day
                    # Need to split the day into departure and arrival
                    # Remove the current entry and next entry, and insert:
                    # current entry (until day-1), day as current city, day as next city, next entry from day+1
                    pass  # complicated, perhaps better to handle during initial itinerary construction
        # The above approach may not capture flight days correctly; alternative approach:
        
        # Alternative approach to build itinerary with flight days:
        itinerary = []
        prev_city = None
        stay_start = None
        for day in range(1, total_days + 1):
            city_idx = m.evaluate(day_city[day]).as_long()
            city = int_to_city[city_idx]
            if prev_city is None:
                prev_city = city
                stay_start = day
            else:
                if city != prev_city:
                    # Flight from prev_city to city on day
                    if stay_start != day - 1:
                        itinerary.append({"day_range": f"Day {stay_start}-{day-1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day-1}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                    stay_start = day
                    prev_city = city
                # else continue the stay
        # Add the last stay
        if stay_start <= total_days:
            if stay_start == total_days:
                itinerary.append({"day_range": f"Day {total_days}", "place": prev_city})
            else:
                itinerary.append({"day_range": f"Day {stay_start}-{total_days}", "place": prev_city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))