from z3 import *
import json

def solve_itinerary():
    # Define the cities and their required days
    cities = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2
    }
    
    # Define the fixed constraints
    fixed_constraints = [
        ("Riga", 5, 8),
        ("Tallinn", 18, 20),
        ("Milan", 24, 26)
    ]
    
    # Define the flight connections
    flight_connections = {
        "Riga": ["Prague", "Milan", "Tallinn", "Warsaw", "Stockholm"],
        "Stockholm": ["Milan", "Lisbon", "Santorini", "Warsaw", "Riga", "Prague", "Tallinn"],
        "Milan": ["Stockholm", "Riga", "Naples", "Porto", "Prague", "Lisbon", "Santorini", "Warsaw"],
        "Lisbon": ["Stockholm", "Warsaw", "Naples", "Porto", "Prague", "Riga", "Milan"],
        "Naples": ["Warsaw", "Milan", "Lisbon", "Santorini"],
        "Warsaw": ["Naples", "Lisbon", "Stockholm", "Riga", "Porto", "Tallinn", "Milan", "Prague"],
        "Porto": ["Lisbon", "Milan", "Warsaw"],
        "Prague": ["Riga", "Tallinn", "Lisbon", "Stockholm", "Milan", "Warsaw"],
        "Tallinn": ["Riga", "Prague", "Stockholm", "Warsaw"],
        "Santorini": ["Stockholm", "Milan", "Naples"]
    }
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Create variables: day_i represents the city on day i (1-based)
    days = 28
    day_vars = [Int(f"day_{i}") for i in range(1, days + 1)]
    
    # Map each city to a unique integer
    city_ids = {city: idx for idx, city in enumerate(cities.keys(), 1)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Add constraints that each day_var must be a valid city id
    for day in day_vars:
        solver.add(Or([day == city_ids[city] for city in cities]))
    
    # Add fixed constraints
    for city, start, end in fixed_constraints:
        for day in range(start, end + 1):
            solver.add(day_vars[day - 1] == city_ids[city])
    
    # Add duration constraints for each city
    for city, duration in cities.items():
        solver.add(Sum([If(day_vars[i] == city_ids[city], 1, 0) for i in range(days)]) == duration
    
    # Add flight transition constraints: consecutive days must be connected by a flight or the same city
    for i in range(days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        solver.add(Or(
            current_day == next_day,  # stay in the same city
            # Or there's a flight connection
            *[
                And(current_day == city_ids[city1], next_day == city_ids[city2])
                for city1 in flight_connections
                for city2 in flight_connections[city1]
            ]
        ))
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        
        # Determine the sequence of cities from the model
        sequence = []
        for i in range(days):
            day_num = i + 1
            city_id = model.evaluate(day_vars[i]).as_long()
            city = id_to_city[city_id]
            sequence.append((day_num, city))
        
        # Generate the itinerary with day ranges
        current_place = sequence[0][1]
        start_day = 1
        
        for i in range(1, days):
            day_num, city = sequence[i]
            if city != current_place:
                # Add the stay for the previous city
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_place})
                # Add the flight day entries (both departure and arrival)
                itinerary.append({"day_range": f"Day {i}", "place": current_place})
                itinerary.append({"day_range": f"Day {i}", "place": city})
                current_place = city
                start_day = i + 1
            # else: continue the stay
        
        # Add the last stay
        if start_day == days:
            itinerary.append({"day_range": f"Day {days}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})
        
        # Post-process to merge consecutive same-city entries where possible
        # This step is more aesthetic and may not be necessary for correctness
        merged_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            entry = itinerary[i]
            if i + 1 < n and itinerary[i+1]['place'] == entry['place']:
                # Merge consecutive entries for the same city
                day_range_parts = []
                current_entry = entry
                j = i
                while j < n and itinerary[j]['place'] == current_entry['place']:
                    day_part = itinerary[j]['day_range']
                    if '-' in day_part:
                        start, end = day_part.replace('Day ', '').split('-')
                        day_range_parts.append((int(start), int(end)))
                    else:
                        day = int(day_part.replace('Day ', ''))
                        day_range_parts.append((day, day))
                    j += 1
                # Combine all parts
                starts = [p[0] for p in day_range_parts]
                ends = [p[1] for p in day_range_parts]
                new_start = min(starts)
                new_end = max(ends)
                if new_start == new_end:
                    new_day_range = f"Day {new_start}"
                else:
                    new_day_range = f"Day {new_start}-{new_end}"
                merged_entry = {'day_range': new_day_range, 'place': current_entry['place']}
                merged_itinerary.append(merged_entry)
                i = j
            else:
                merged_itinerary.append(entry)
                i += 1
        
        # Further adjust for flight days (where the same day appears for two cities)
        # Ensure flight days are correctly represented with separate entries
        final_itinerary = []
        i = 0
        n = len(merged_itinerary)
        while i < n:
            entry = merged_itinerary[i]
            if i < n - 1:
                next_entry = merged_itinerary[i + 1]
                current_day = entry['day_range']
                next_day = next_entry['day_range']
                # Check if they share a day (flight day)
                if '-' not in current_day and '-' not in next_day and current_day == next_day:
                    # It's a flight day, keep both entries
                    final_itinerary.append(entry)
                    final_itinerary.append(next_entry)
                    i += 2
                    continue
            final_itinerary.append(entry)
            i += 1
        
        return {"itinerary": final_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))