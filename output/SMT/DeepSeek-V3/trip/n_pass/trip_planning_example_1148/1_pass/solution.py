from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Lisbon": 2,
        "Dubrovnik": 5,
        "Copenhagen": 5,
        "Prague": 3,
        "Tallinn": 2,
        "Stockholm": 4,
        "Split": 3,
        "Lyon": 2
    }
    
    # Direct flights
    direct_flights = {
        "Dubrovnik": ["Stockholm", "Copenhagen"],
        "Lisbon": ["Copenhagen", "Lyon", "Stockholm", "Prague"],
        "Copenhagen": ["Lisbon", "Stockholm", "Split", "Dubrovnik", "Prague", "Tallinn"],
        "Prague": ["Stockholm", "Lyon", "Lisbon", "Copenhagen", "Split"],
        "Tallinn": ["Stockholm", "Copenhagen", "Prague"],
        "Stockholm": ["Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Lisbon", "Split"],
        "Split": ["Copenhagen", "Stockholm", "Prague", "Lyon"],
        "Lyon": ["Lisbon", "Prague", "Split"]
    }
    
    # Event constraints
    # Workshop in Lisbon between day 4 and 5 (i.e., must be in Lisbon on day 4 or 5)
    # Meeting in Tallinn between day 1 and 2 (i.e., must be in Tallinn on day 1 or 2)
    # Wedding in Stockholm between day 13 and 16 (i.e., must be in Stockholm on one of these days)
    # Annual show in Lyon from day 18 to 19 (i.e., must be in Lyon on day 18 and 19)
    
    # Create Z3 variables: for each day, which city are we in?
    # We'll model each day's city as an integer (indexing into the cities list)
    city_list = list(cities.keys())
    city_to_idx = {city: idx for idx, city in enumerate(city_list)}
    n_days = 19
    n_cities = len(city_list)
    
    # For each day, the city we're in (before considering flights)
    day_city = [Int(f"day_{day}_city") for day in range(1, n_days + 1)]
    
    # Flight transitions: for each day, whether we fly (and to which city)
    # flight_to[day] is the city we fly to on that day (or -1 if no flight)
    flight_to = [Int(f"flight_to_{day}") for day in range(1, n_days + 1)]
    
    s = Solver()
    
    # Constraints for day_city and flight_to
    for day in range(1, n_days + 1):
        # day_city must be a valid city index
        s.add(And(day_city[day-1] >= 0, day_city[day-1] < n_cities))
        # flight_to must be -1 (no flight) or a valid city index different from current city
        s.add(Or(
            flight_to[day-1] == -1,
            And(flight_to[day-1] >= 0, flight_to[day-1] < n_cities, flight_to[day-1] != day_city[day-1])
        )
        # If flight_to is not -1, then there must be a direct flight between day_city and flight_to
        for city_idx in range(n_cities):
            for to_city_idx in range(n_cities):
                if city_idx == to_city_idx:
                    continue
                from_city = city_list[city_idx]
                to_city = city_list[to_city_idx]
                if to_city not in direct_flights[from_city]:
                    s.add(Not(And(day_city[day-1] == city_idx, flight_to[day-1] == to_city_idx)))
    
    # Constraints for consecutive days in the same city (no flight)
    # Also, flights can't happen on consecutive days (simplifying assumption)
    for day in range(1, n_days):
        # If flight_to[day] is not -1, then day_city[day+1] must be flight_to[day]
        s.add(If(flight_to[day-1] != -1,
                 day_city[day] == flight_to[day-1],
                 day_city[day] == day_city[day-1]))
    
    # Constraints for total days in each city
    for city, required_days in cities.items():
        city_idx = city_to_idx[city]
        total_days = 0
        for day in range(1, n_days + 1):
            # The city is counted if day_city[day-1] is the city or if flight_to[day-1] is the city
            total_days += If(Or(day_city[day-1] == city_idx, 
                               And(flight_to[day-1] == city_idx, flight_to[day-1] != -1)), 1, 0)
        s.add(total_days == required_days)
    
    # Event constraints
    # Workshop in Lisbon between day 4 and 5: must be in Lisbon on day 4 or 5 (or both)
    lisbon_idx = city_to_idx["Lisbon"]
    s.add(Or(
        day_city[3] == lisbon_idx,  # day 4
        day_city[4] == lisbon_idx,  # day 5
        And(flight_to[3] == lisbon_idx),  # flying to Lisbon on day 4
        And(flight_to[4] == lisbon_idx)   # flying to Lisbon on day 5
    ))
    
    # Meeting in Tallinn between day 1 and 2: must be in Tallinn on day 1 or 2
    tallinn_idx = city_to_idx["Tallinn"]
    s.add(Or(
        day_city[0] == tallinn_idx,  # day 1
        day_city[1] == tallinn_idx,  # day 2
        And(flight_to[0] == tallinn_idx),  # flying to Tallinn on day 1
        And(flight_to[1] == tallinn_idx)   # flying to Tallinn on day 2
    ))
    
    # Wedding in Stockholm between day 13 and 16: must be in Stockholm on at least one of these days
    stockholm_idx = city_to_idx["Stockholm"]
    s.add(Or(
        day_city[12] == stockholm_idx,  # day 13
        day_city[13] == stockholm_idx,  # day 14
        day_city[14] == stockholm_idx,  # day 15
        day_city[15] == stockholm_idx,  # day 16
        And(flight_to[12] == stockholm_idx),  # day 13
        And(flight_to[13] == stockholm_idx),  # day 14
        And(flight_to[14] == stockholm_idx),  # day 15
        And(flight_to[15] == stockholm_idx)   # day 16
    ))
    
    # Annual show in Lyon from day 18 to 19: must be in Lyon on day 18 and 19
    lyon_idx = city_to_idx["Lyon"]
    s.add(And(
        Or(day_city[17] == lyon_idx, And(flight_to[17] == lyon_idx)),  # day 18
        Or(day_city[18] == lyon_idx, And(flight_to[18] == lyon_idx))   # day 19
    ))
    # Additionally, no flight on day 19 (since the show is on day 18-19, and we can't fly on day 19)
    s.add(flight_to[18] == -1)
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        # Extract the itinerary
        itinerary = []
        current_city = None
        start_day = 1
        for day in range(1, n_days + 1):
            city_idx = m.evaluate(day_city[day-1]).as_long()
            city = city_list[city_idx]
            flight = m.evaluate(flight_to[day-1])
            if flight.as_long() != -1:
                to_city_idx = flight.as_long()
                to_city = city_list[to_city_idx]
                # Add entry for the current city up to this day (flight day)
                if start_day <= day:
                    if start_day == day:
                        itinerary.append({"day_range": f"Day {day}", "place": city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day}", "place": city})
                # Add flight day entries for departure and arrival
                itinerary.append({"day_range": f"Day {day}", "place": city})
                itinerary.append({"day_range": f"Day {day}", "place": to_city})
                start_day = day + 1
                current_city = to_city
            else:
                if day == n_days:
                    if start_day == day:
                        itinerary.append({"day_range": f"Day {day}", "place": city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day}", "place": city})
        # Post-process to merge consecutive days in the same city
        optimized_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            current = itinerary[i]
            if i + 1 < n and itinerary[i+1]['place'] == current['place']:
                # Merge consecutive entries for the same city
                start_day = current['day_range'].split('-')[0].split(' ')[1]
                j = i + 1
                while j < n and itinerary[j]['place'] == current['place']:
                    j += 1
                end_day = itinerary[j-1]['day_range'].split('-')[-1]
                if '-' in current['day_range']:
                    start_day = current['day_range'].split('-')[0].split(' ')[1]
                new_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
                optimized_itinerary.append({"day_range": new_range, "place": current['place']})
                i = j
            else:
                optimized_itinerary.append(current)
                i += 1
        # Handle flight days (where the same day appears for two cities)
        final_itinerary = []
        i = 0
        while i < len(optimized_itinerary):
            current = optimized_itinerary[i]
            if i + 1 < len(optimized_itinerary):
                next_entry = optimized_itinerary[i+1]
                if current['day_range'] == next_entry['day_range']:
                    # Flight day: add both entries
                    final_itinerary.append(current)
                    final_itinerary.append(next_entry)
                    i += 2
                    continue
            final_itinerary.append(current)
            i += 1
        return {"itinerary": final_itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))