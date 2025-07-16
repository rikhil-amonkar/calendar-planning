from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Paris": 6,
        "Oslo": 5,
        "Porto": 7,
        "Geneva": 7,
        "Reykjavik": 2
    }
    
    # Direct flights
    direct_flights = [
        ("Paris", "Oslo"),
        ("Geneva", "Oslo"),
        ("Porto", "Paris"),
        ("Geneva", "Paris"),
        ("Geneva", "Porto"),
        ("Paris", "Reykjavik"),
        ("Reykjavik", "Oslo"),
        ("Porto", "Oslo")
    ]
    # Make flights bidirectional
    bidirectional_flights = []
    for a, b in direct_flights:
        bidirectional_flights.append((a, b))
        bidirectional_flights.append((b, a))
    direct_flights_set = set(bidirectional_flights)
    
    total_days = 23
    
    # Create Z3 variables: city for each day
    day_city = [Int(f"day_{i}_city") for i in range(1, total_days + 1)]
    
    # Mapping city names to integers
    city_to_int = {
        "Paris": 0,
        "Oslo": 1,
        "Porto": 2,
        "Geneva": 3,
        "Reykjavik": 4
    }
    int_to_city = {v: k for k, v in city_to_int.items()}
    
    s = Solver()
    
    # Each day's city must be 0-4
    for day in day_city:
        s.add(day >= 0, day <=4)
    
    # Constraints for days in each city
    for city, days in cities.items():
        c = city_to_int[city]
        s.add(Sum([If(day == c, 1, 0) for day in day_city]) == days)
    
    # Conference in Geneva from day 1 to 7
    for i in range(7):
        s.add(day_city[i] == city_to_int["Geneva"])
    
    # Relatives in Oslo between day 19 and 23 (inclusive)
    # At least one day in Oslo in 19-23
    s.add(Or([day_city[i] == city_to_int["Oslo"] for i in range(18, 23)]))  # days are 1-based, but Python is 0-based
    
    # Flight transitions: consecutive days can only change to directly connected cities
    for i in range(total_days - 1):
        current_city = day_city[i]
        next_city = day_city[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_to_int[a], next_city == city_to_int[b])
                for a, b in direct_flights_set
            ]
        ))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        for day in range(1, total_days + 1):
            city_int = m.evaluate(day_city[day - 1]).as_long()
            city = int_to_city[city_int]
            if city != current_city:
                if current_city is not None:
                    # Add the previous stay
                    if start_day == day - 1:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day - 1}", "place": current_city})
                    # Add the flight day for the previous city
                    itinerary.append({"day_range": f"Day {day - 1}", "place": current_city})
                # Add the flight day for the new city
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_city = city
                start_day = day
        # Add the last stay
        if start_day == total_days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        
        # Now, we need to handle flight days properly. For example, if day X is a flight day between A and B, then day X should appear as both A and B.
        # So, we need to process the itinerary to split flight days.
        # Reconstruct the itinerary properly.
        final_itinerary = []
        prev_day_place = None
        for entry in itinerary:
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                for day in range(start, end + 1):
                    final_itinerary.append({"day_range": f"Day {day}", "place": place})
            else:
                day = int(day_range.replace("Day ", ""))
                final_itinerary.append({"day_range": f"Day {day}", "place": place})
        
        # Now, for flight days, if consecutive entries have the same day but different places, it's a flight.
        # We need to group by day and for each day, list all places.
        day_places = {}
        for entry in final_itinerary:
            day = entry["day_range"]
            place = entry["place"]
            if day not in day_places:
                day_places[day] = []
            if place not in day_places[day]:
                day_places[day].append(place)
        
        # Now, rebuild the itinerary with flight days handled.
        new_itinerary = []
        processed_days = set()
        for day in sorted(day_places.keys(), key=lambda x: int(x.split()[1])):
            places = day_places[day]
            if len(places) == 1:
                new_itinerary.append({"day_range": day, "place": places[0]})
            else:
                for place in places:
                    new_itinerary.append({"day_range": day, "place": place})
        
        # Now, compress consecutive days with the same place into ranges.
        compressed_itinerary = []
        if not new_itinerary:
            return {"itinerary": []}
        
        current_place = new_itinerary[0]["place"]
        start_day = int(new_itinerary[0]["day_range"].split()[1])
        prev_day = start_day
        
        for entry in new_itinerary[1:]:
            day = int(entry["day_range"].split()[1])
            place = entry["place"]
            if place == current_place and day == prev_day + 1:
                prev_day = day
            else:
                if start_day == prev_day:
                    compressed_itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    compressed_itinerary.append({"day_range": f"Day {start_day}-{prev_day}", "place": current_place})
                # Check if the current entry is part of a flight (same day as previous)
                if day == prev_day:
                    # It's a flight day, so add separately
                    pass
                current_place = place
                start_day = day
                prev_day = day
        # Add the last entry
        if start_day == prev_day:
            compressed_itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            compressed_itinerary.append({"day_range": f"Day {start_day}-{prev_day}", "place": current_place})
        
        # Now, handle flight days by adding separate entries for departure and arrival.
        # We need to look for days that appear multiple times in new_itinerary.
        flight_days = {}
        for entry in new_itinerary:
            day = entry["day_range"]
            place = entry["place"]
            if day not in flight_days:
                flight_days[day] = []
            flight_days[day].append(place)
        
        final_compressed = []
        i = 0
        n = len(compressed_itinerary)
        while i < n:
            entry = compressed_itinerary[i]
            day_range = entry["day_range"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                # Check if any day in this range is a flight day
                flight_in_range = any(len(flight_days.get(f"Day {day}", [])) > 1 for day in range(start, end + 1))
                if not flight_in_range:
                    final_compressed.append(entry)
                    i += 1
                else:
                    # Split into non-flight and flight parts
                    current_start = start
                    for day in range(start, end + 1):
                        day_str = f"Day {day}"
                        if len(flight_days.get(day_str, [])) > 1:
                            # Days before flight
                            if day > current_start:
                                final_compressed.append({"day_range": f"Day {current_start}-{day - 1}", "place": entry["place"]})
                            # Flight day
                            for place in flight_days[day_str]:
                                final_compressed.append({"day_range": day_str, "place": place})
                            current_start = day + 1
                    if current_start <= end:
                        final_compressed.append({"day_range": f"Day {current_start}-{end}", "place": entry["place"]})
                    i += 1
            else:
                day = int(day_range.split()[1])
                day_str = f"Day {day}"
                if len(flight_days.get(day_str, [])) > 1:
                    # It's a flight day
                    for place in flight_days[day_str]:
                        final_compressed.append({"day_range": day_str, "place": place})
                else:
                    final_compressed.append(entry)
                i += 1
        
        return {"itinerary": final_compressed}
    else:
        return {"itinerary": []}

result = solve_itinerary()
print(json.dumps(result, indent=2))