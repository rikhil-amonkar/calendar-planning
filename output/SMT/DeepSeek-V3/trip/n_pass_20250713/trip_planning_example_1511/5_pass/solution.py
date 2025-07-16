from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }
    
    # Direct flights (undirected)
    direct_flights = {
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
    }
    
    # Create a dictionary for quick lookup of connected cities
    connected = {}
    for city in cities:
        connected[city] = []
    for a, b in direct_flights:
        if a in cities and b in cities:
            connected[a].append(b)
            connected[b].append(a)
    
    total_days = 24
    days = list(range(1, total_days + 1))
    
    # Create a solver instance
    s = Solver()
    
    # Variables: for each city, the start and end days of the stay
    start = {city: Int(f'start_{city}') for city in cities}
    end = {city: Int(f'end_{city}') for city in cities}
    
    # Constraints for start and end days
    for city in cities:
        s.add(start[city] >= 1)
        s.add(end[city] <= total_days)
        s.add(end[city] == start[city] + cities[city] - 1)
    
    # All intervals for cities are disjoint except for flight days (handled via sequence)
    for city1 in cities:
        for city2 in cities:
            if city1 == city2:
                continue
            # Either city1 is before city2, or vice versa, or they overlap on exactly one day (flight day)
            case1 = end[city1] < start[city2]
            case2 = end[city2] < start[city1]
            case3 = And(
                end[city1] == start[city2],
                (city1, city2) in direct_flights or (city2, city1) in direct_flights
            )
            case4 = And(
                end[city2] == start[city1],
                (city1, city2) in direct_flights or (city2, city1) in direct_flights
            )
            s.add(Or(case1, case2, case3, case4))
    
    # Fixed constraints:
    # Munich from day 4 to day 6
    s.add(start["Munich"] == 4)
    s.add(end["Munich"] == 6)
    
    # Santorini between day 8 and day 10 (so start <= 8, end >=10)
    s.add(start["Santorini"] <= 8)
    s.add(end["Santorini"] >= 10)
    
    # Workshop in Valencia between day 14 and 15 (2 days: 14-15)
    s.add(start["Valencia"] <= 14)
    s.add(end["Valencia"] >= 15)
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        # Extract start and end days for each city
        starts = {city: m.evaluate(start[city]).as_long() for city in cities}
        ends = {city: m.evaluate(end[city]).as_long() for city in cities}
        
        # Generate the itinerary
        itinerary = []
        
        # Collect all intervals
        intervals = []
        for city in cities:
            s_day = starts[city]
            e_day = ends[city]
            intervals.append((s_day, e_day, city))
        
        # Also, for flight days, we need to find days where two cities' intervals meet (end of one is start of another)
        flight_days = set()
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    if ends[city1] == starts[city2] and ((city1, city2) in direct_flights or (city2, city1) in direct_flights):
                        flight_days.add((ends[city1], city1, city2))
        
        # Now, build the itinerary
        # First, sort all intervals by start day
        intervals.sort()
        
        # For each day, determine which cities are visited
        day_to_cities = {}
        for day in range(1, total_days + 1):
            day_to_cities[day] = []
            for s_day, e_day, city in intervals:
                if s_day <= day <= e_day:
                    day_to_cities[day].append(city)
        
        # Also, add flight transitions
        for flight_day, city1, city2 in flight_days:
            day_to_cities[flight_day].append(city2)
        
        # Now, build the itinerary by grouping consecutive days with the same set of cities
        current_places = []
        current_start = 1
        itinerary_json = []
        
        for day in range(1, total_days + 1):
            places = day_to_cities[day]
            if set(places) != set(current_places):
                if current_places:
                    if current_start == day - 1:
                        itinerary_json.append({"day_range": f"Day {current_start}", "place": current_places[0]})
                    else:
                        itinerary_json.append({"day_range": f"Day {current_start}-{day - 1}", "place": current_places[0]})
                current_places = places
                current_start = day
        # Add the last interval
        if current_places:
            if current_start == total_days:
                itinerary_json.append({"day_range": f"Day {current_start}", "place": current_places[0]})
            else:
                itinerary_json.append({"day_range": f"Day {current_start}-{total_days}", "place": current_places[0]})
        
        # Now, handle flight days by adding separate entries for departure and arrival cities
        # Reconstruct the itinerary with flight days split
        final_itinerary = []
        i = 0
        while i < len(itinerary_json):
            entry = itinerary_json[i]
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start_day, end_day = map(int, day_range.replace("Day ", "").split('-'))
                days_in_segment = list(range(start_day, end_day + 1))
            else:
                start_day = end_day = int(day_range.replace("Day ", ""))
                days_in_segment = [start_day]
            
            # Check if any of these days are flight days
            flight_days_in_segment = []
            for day in days_in_segment:
                cities_on_day = day_to_cities[day]
                if len(cities_on_day) > 1:
                    flight_days_in_segment.append(day)
            
            if not flight_days_in_segment:
                final_itinerary.append(entry)
                i += 1
            else:
                # Split the segment around flight days
                current_start = start_day
                for flight_day in sorted(flight_days_in_segment):
                    if current_start < flight_day:
                        # Add segment before flight day
                        if current_start == flight_day - 1:
                            final_itinerary.append({"day_range": f"Day {current_start}", "place": place})
                        else:
                            final_itinerary.append({"day_range": f"Day {current_start}-{flight_day - 1}", "place": place})
                    # Add flight day entries
                    cities_on_flight_day = day_to_cities[flight_day]
                    for city in cities_on_flight_day:
                        final_itinerary.append({"day_range": f"Day {flight_day}", "place": city})
                    current_start = flight_day + 1
                # Add remaining days after last flight day in segment
                if current_start <= end_day:
                    if current_start == end_day:
                        final_itinerary.append({"day_range": f"Day {current_start}", "place": place})
                    else:
                        final_itinerary.append({"day_range": f"Day {current_start}-{end_day}", "place": place})
                i += 1
        
        # The above may duplicate some entries, so we need to merge consecutive same-place entries
        merged_itinerary = []
        if not final_itinerary:
            return {"itinerary": []}
        
        current_entry = final_itinerary[0]
        for next_entry in final_itinerary[1:]:
            if current_entry["place"] == next_entry["place"]:
                # Merge day ranges
                current_day_range = current_entry["day_range"]
                next_day_range = next_entry["day_range"]
                current_start = int(current_day_range.replace("Day ", "").split('-')[0])
                current_end = current_start
                if '-' in current_day_range:
                    current_start, current_end = map(int, current_day_range.replace("Day ", "").split('-'))
                next_start = int(next_day_range.replace("Day ", "").split('-')[0])
                next_end = next_start
                if '-' in next_day_range:
                    next_start, next_end = map(int, next_day_range.replace("Day ", "").split('-'))
                if current_end + 1 == next_start:
                    new_day_range = f"Day {current_start}-{next_end}"
                    current_entry = {"day_range": new_day_range, "place": current_entry["place"]}
                else:
                    merged_itinerary.append(current_entry)
                    current_entry = next_entry
            else:
                merged_itinerary.append(current_entry)
                current_entry = next_entry
        merged_itinerary.append(current_entry)
        
        return {"itinerary": merged_itinerary}
    else:
        return {"itinerary": []}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))