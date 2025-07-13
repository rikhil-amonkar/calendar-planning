from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Porto": 5,
        "Prague": 4,
        "Reykjavik": 4,
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 4
    }
    
    # Direct flights: adjacency list
    direct_flights = {
        "Porto": ["Amsterdam", "Munich"],
        "Amsterdam": ["Porto", "Munich", "Reykjavik", "Santorini", "Prague"],
        "Munich": ["Amsterdam", "Porto", "Reykjavik", "Prague"],
        "Reykjavik": ["Amsterdam", "Munich", "Prague"],
        "Prague": ["Reykjavik", "Amsterdam", "Munich"],
        "Santorini": ["Amsterdam"]
    }
    
    total_days = 16
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Variables: for each day, which city are we in?
    # day_cities[d][c] is True if we are in city c on day d+1 (days are 1-based)
    day_cities = [[Bool(f"day_{day+1}_{city}") for city in cities] for day in range(total_days)]
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Each day, at least one city is visited (but possibly two on flight days)
    for day in range(total_days):
        s.add(Or([day_cities[day][i] for i in range(len(cities))]))
    
    # Flight days: if two cities are true on the same day, they must be connected by a direct flight
    for day in range(total_days):
        for c1 in range(len(cities)):
            for c2 in range(c1 + 1, len(cities)):
                city1 = list(cities.keys())[c1]
                city2 = list(cities.keys())[c2]
                # If both cities are true on this day, they must have a direct flight
                s.add(Implies(And(day_cities[day][c1], day_cities[day][c2]), 
                      Or([city2 in direct_flights[city1], city1 in direct_flights[city2]]))
    
    # Total days per city must match requirements
    for city, days in cities.items():
        idx = city_indices[city]
        total = 0
        for day in range(total_days):
            total += If(day_cities[day][idx], 1, 0)
        s.add(total == days)
    
    # Constraints for events:
    # Wedding in Reykjavik between day 4 and 7 (inclusive): at least one of days 4,5,6,7 is in Reykjavik
    reykjavik_idx = city_indices["Reykjavik"]
    s.add(Or([day_cities[day][reykjavik_idx] for day in range(3, 7)]))  # days 4-7 (0-based 3-6)
    
    # Conference in Amsterdam on day 14 and 15
    amsterdam_idx = city_indices["Amsterdam"]
    s.add(day_cities[13][amsterdam_idx])  # day 14
    s.add(day_cities[14][amsterdam_idx])  # day 15
    
    # Friend in Munich between day 7 and 10 (inclusive)
    munich_idx = city_indices["Munich"]
    s.add(Or([day_cities[day][munich_idx] for day in range(6, 10)]))  # days 7-10 (0-based 6-9)
    
    # No two consecutive flight days (optional, but helps avoid unnecessary complexity)
    for day in range(total_days - 1):
        # Count the number of cities per day
        day1_count = Sum([If(day_cities[day][i], 1, 0) for i in range(len(cities))])
        day2_count = Sum([If(day_cities[day+1][i], 1, 0) for i in range(len(cities))])
        s.add(Or(day1_count == 1, day2_count == 1))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Extract the itinerary
        itinerary = []
        
        # Determine for each day which cities are visited
        day_places = []
        for day in range(total_days):
            current_day = day + 1
            cities_in_day = []
            for city in cities:
                idx = city_indices[city]
                if m.evaluate(day_cities[day][idx]):
                    cities_in_day.append(city)
            day_places.append((current_day, cities_in_day))
        
        # Now, build the itinerary with day ranges
        current_place = None
        start_day = None
        
        # Process each day and handle flight days
        for day, places in day_places:
            if len(places) == 1:
                place = places[0]
                if current_place != place:
                    if current_place is not None:
                        # End previous stay
                        itinerary.append({
                            "day_range": f"Day {start_day}-{day-1}",
                            "place": current_place
                        })
                    # Start new stay
                    current_place = place
                    start_day = day
            else:
                # Flight day: two places
                if current_place is not None:
                    # End previous stay up to day-1
                    if start_day <= day - 1:
                        itinerary.append({
                            "day_range": f"Day {start_day}-{day-1}",
                            "place": current_place
                        })
                # Add flight day entries for both places
                place1, place2 = places
                itinerary.append({
                    "day_range": f"Day {day}",
                    "place": place1
                })
                itinerary.append({
                    "day_range": f"Day {day}",
                    "place": place2
                })
                # The next stay starts at day+1 for the arrival city
                current_place = place2
                start_day = day + 1
        
        # Add the last stay if it's a single place
        if current_place is not None and start_day <= total_days:
            itinerary.append({
                "day_range": f"Day {start_day}-{total_days}",
                "place": current_place
            })
        
        # Now, handle cases where flight days are at the end
        # Also, ensure that consecutive entries are merged if possible
        # But per the problem's note, flight days are separate entries
        
        # The itinerary may need adjustments for multi-city days
        # So, re-parse day_places to create the exact required output
        final_itinerary = []
        for day, places in day_places:
            current_day = day
            for place in places:
                # Check if this place is part of a continuous stay
                # For flight days, add individual day entries
                if len(places) > 1:
                    final_itinerary.append({
                        "day_range": f"Day {day+1}",
                        "place": place
                    })
                else:
                    # Check if this place continues from previous or next days
                    pass
        
        # Now, group consecutive days for the same place without flight days in between
        # Reconstruct the itinerary properly
        final_itinerary = []
        i = 0
        n = len(day_places)
        while i < n:
            day, places = day_places[i]
            current_day_start = day
            if len(places) == 1:
                place = places[0]
                j = i + 1
                while j < n and len(day_places[j][1]) == 1 and day_places[j][1][0] == place:
                    j += 1
                end_day = day_places[j-1][0]
                final_itinerary.append({
                    "day_range": f"Day {current_day_start}-{end_day}",
                    "place": place
                })
                i = j
            else:
                place1, place2 = places
                final_itinerary.append({
                    "day_range": f"Day {day}",
                    "place": place1
                })
                final_itinerary.append({
                    "day_range": f"Day {day}",
                    "place": place2
                })
                i += 1
        
        # Now, also add the individual day entries for flight days
        # So, for each day in day_places, if it's a flight day, add both places for that day
        # Then, for consecutive days in the same place, merge them
        # So first, collect all individual day entries
        expanded_entries = []
        for day, places in day_places:
            for place in places:
                expanded_entries.append((day + 1, place))  # days are 1-based
        
        # Now, group consecutive days for the same place
        if not expanded_entries:
            return {"itinerary": []}
        
        current_place = expanded_entries[0][1]
        start_day = expanded_entries[0][0]
        final_itinerary = []
        
        for i in range(1, len(expanded_entries)):
            day, place = expanded_entries[i]
            if place == current_place and day == expanded_entries[i-1][0] + 1:
                continue  # part of the same block
            else:
                # Close the previous block
                end_day = expanded_entries[i-1][0]
                if start_day == end_day:
                    final_itinerary.append({
                        "day_range": f"Day {start_day}",
                        "place": current_place
                    })
                else:
                    final_itinerary.append({
                        "day_range": f"Day {start_day}-{end_day}",
                        "place": current_place
                    })
                # Start new block
                current_place = place
                start_day = day
        
        # Add the last block
        end_day = expanded_entries[-1][0]
        if start_day == end_day:
            final_itinerary.append({
                "day_range": f"Day {start_day}",
                "place": current_place
            })
        else:
            final_itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": current_place
            })
        
        # Now, insert the flight days (days with two places) as separate entries
        # So, reparse day_places to find days with two cities and insert them
        temp_itinerary = []
        flight_days = set()
        for day, places in day_places:
            if len(places) == 2:
                flight_days.add(day + 1)  # 1-based
        
        # Now, build the itinerary again, but for flight days, insert both places
        # We need to merge the expanded entries and split flight days
        new_itinerary = []
        i = 0
        while i < len(final_itinerary):
            entry = final_itinerary[i]
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start, end = map(int, day_range.split('-')[0].split('Day ')[1].split('-'))
                days_in_block = list(range(start, end + 1))
            else:
                day = int(day_range.split('Day ')[1])
                days_in_block = [day]
            
            # Check if any of these days are flight days
            flight_days_in_block = [d for d in days_in_block if d in flight_days]
            if not flight_days_in_block:
                new_itinerary.append(entry)
                i += 1
            else:
                # Split the block into non-flight and flight days
                current_start = days_in_block[0]
                for day in days_in_block:
                    if day in flight_days:
                        if current_start <= day - 1:
                            new_itinerary.append({
                                "day_range": f"Day {current_start}-{day - 1}",
                                "place": place
                            })
                        # Add flight day entries
                        flight_places = next(p for d, p in day_places if d + 1 == day)
                        for fp in flight_places:
                            new_itinerary.append({
                                "day_range": f"Day {day}",
                                "place": fp
                            })
                        current_start = day + 1
                    # Handle last day
                if current_start <= days_in_block[-1]:
                    new_itinerary.append({
                        "day_range": f"Day {current_start}-{days_in_block[-1]}",
                        "place": place
                    })
                i += 1
        
        # Now, ensure that for flight days, both cities are listed for that day
        # Also, remove duplicate entries (if any)
        # Also, ensure the ordering is correct
        unique_entries = []
        seen = set()
        for entry in new_itinerary:
            key = (entry["day_range"], entry["place"])
            if key not in seen:
                seen.add(key)
                unique_entries.append(entry)
        
        # Now, order the entries by day
        def get_day(day_str):
            if '-' in day_str:
                return int(day_str.split('-')[0].split('Day ')[1])
            else:
                return int(day_str.split('Day ')[1])
        
        unique_entries.sort(key=lambda x: get_day(x["day_range"]))
        
        return {"itinerary": unique_entries}
    else:
        return {"itinerary": []}

# Execute the solver
result = solve_itinerary()
print(json.dumps(result, indent=2))