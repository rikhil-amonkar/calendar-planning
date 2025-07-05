from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Frankfurt": 4,
        "Manchester": 4,
        "Valencia": 4,
        "Naples": 4,
        "Oslo": 3,
        "Vilnius": 2
    }
    
    # Direct flights
    direct_flights = {
        "Valencia": ["Frankfurt", "Naples"],
        "Manchester": ["Frankfurt", "Naples", "Oslo"],
        "Naples": ["Manchester", "Frankfurt", "Oslo", "Valencia"],
        "Oslo": ["Naples", "Frankfurt", "Vilnius", "Manchester"],
        "Vilnius": ["Frankfurt", "Oslo"],
        "Frankfurt": ["Valencia", "Manchester", "Naples", "Oslo", "Vilnius"]
    }
    
    # Correcting Naples's entry (spelling of Frankfurt)
    direct_flights["Naples"] = ["Manchester", "Frankfurt", "Oslo", "Valencia"]
    
    num_days = 16
    days = list(range(1, num_days + 1))
    
    # Create Z3 variables: day_to_city[d] is the city for day d
    day_to_city = {d: Int(f'day_{d}_city') for d in days}
    
    # City to integer mapping
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    s = Solver()
    
    # Each day's city must be one of the six cities
    for d in days:
        s.add(Or([day_to_city[d] == city_ids[city] for city in cities]))
    
    # Constraints for total days per city
    for city, required_days in cities.items():
        total = Sum([If(day_to_city[d] == city_ids[city], 1, 0) for d in days])
        s.add(total == required_days)
    
    # Frankfurt must be days 13-16
    for d in range(13, 17):
        s.add(day_to_city[d] == city_ids["Frankfurt"])
    
    # Vilnius must be day 12 or 13 (wedding between day 12 and 13)
    s.add(Or(day_to_city[12] == city_ids["Vilnius"], day_to_city[13] == city_ids["Vilnius"]))
    
    # Flight constraints: consecutive days can only be same city or connected by direct flight
    for d in range(1, num_days):
        current_city = day_to_city[d]
        next_city = day_to_city[d + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_ids[city1], next_city == city_ids[city2])
                for city1 in cities
                for city2 in direct_flights.get(city1, [])
            ]
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Decode the model into a day-to-city list
        itinerary_days = []
        for d in days:
            city_id = m.evaluate(day_to_city[d]).as_long()
            itinerary_days.append(id_to_city[city_id])
        
        # Now, generate the itinerary in the required JSON format
        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1
        
        for d in range(1, num_days):
            if itinerary_days[d] == current_place:
                continue
            else:
                end_day = d
                if start_day == end_day:
                    day_str = f"Day {start_day}"
                else:
                    day_str = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_str, "place": current_place})
                # Add the flight day entries
                # Day d is the transition day: current_place and next place
                itinerary.append({"day_range": f"Day {d}", "place": current_place})
                itinerary.append({"day_range": f"Day {d}", "place": itinerary_days[d]})
                current_place = itinerary_days[d]
                start_day = d + 1
        
        # Add the last segment
        end_day = num_days
        if start_day == end_day:
            day_str = f"Day {start_day}"
        else:
            day_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_str, "place": current_place})
        
        # Verify day counts
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            if '-' in entry['day_range']:
                start, end = map(int, entry['day_range'].replace("Day ", "").split('-'))
                days_in_segment = end - start + 1
            else:
                days_in_segment = 1
            day_counts[entry['place']] += days_in_segment
        
        # Adjust for flight days (each flight day is counted for both cities)
        # So no adjustment needed here since the model already counts each day for each city correctly
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))