from z3 import *
import json

def solve_itinerary():
    # Cities involved
    cities = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    
    # Direct flight connections (undirected)
    direct_flights = {
        "Prague": ["Tallinn", "Zurich", "Florence", "Bucharest", "Frankfurt"],
        "Tallinn": ["Prague", "Frankfurt", "Zurich"],
        "Zurich": ["Prague", "Bucharest", "Venice", "Frankfurt", "Florence", "Tallinn"],
        "Florence": ["Prague", "Frankfurt", "Zurich"],
        "Frankfurt": ["Bucharest", "Venice", "Tallinn", "Zurich", "Prague", "Florence"],
        "Bucharest": ["Frankfurt", "Prague", "Zurich"],
        "Venice": ["Frankfurt", "Zurich"]
    }
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Days are from 1 to 26
    days = 26
    Day = IntSort()
    
    # Create a Z3 array where each day (1..26) is mapped to a city (represented by an integer)
    city_map = Array('city_map', Day, IntSort())
    
    # Assign each city to an integer for easier handling
    city_ids = {city: idx for idx, city in enumerate(cities)}
    
    # Constraints for each day's city assignment
    for day in range(1, days + 1):
        solver.add(And(city_map[day] >= 0, city_map[day] < len(cities)))
    
    # Fixed constraints
    # Venice must be visited between days 22-26 (inclusive)
    for day in range(22, 27):
        solver.add(city_map[day] == city_ids["Venice"])
    
    # Frankfurt must be visited between days 12-16 (inclusive)
    for day in range(12, 17):
        solver.add(city_map[day] == city_ids["Frankfurt"])
    
    # Tallinn must be visited between days 8-12 (inclusive)
    for day in range(8, 13):
        solver.add(city_map[day] == city_ids["Tallinn"])
    
    # Count the days spent in each city
    counts = {city: 0 for city in cities}
    for city in cities:
        counts[city] = Sum([If(city_map[day] == city_ids[city], 1, 0) for day in range(1, days + 1)])
    
    solver.add(counts["Bucharest"] == 3)
    solver.add(counts["Venice"] == 5)
    solver.add(counts["Prague"] == 4)
    solver.add(counts["Frankfurt"] == 5)
    solver.add(counts["Zurich"] == 5)
    solver.add(counts["Florence"] == 5)
    solver.add(counts["Tallinn"] == 5)
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for day in range(1, days):
        current_city = city_map[day]
        next_city = city_map[day + 1]
        # If the city changes, there must be a direct flight
        solver.add(Implies(current_city != next_city, 
                           Or([And(current_city == city_ids[c1], next_city == city_ids[c2]) 
                              for c1 in direct_flights for c2 in direct_flights[c1]])))
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        # Extract the itinerary
        itinerary = []
        current_place = None
        start_day = 1
        
        # Helper to add entries to itinerary
        def add_entry(day_range, place):
            itinerary.append({"day_range": day_range, "place": place})
        
        # Generate day ranges
        for day in range(1, days + 1):
            city_idx = model.eval(city_map[day]).as_long()
            city = cities[city_idx]
            if day == 1:
                current_place = city
                start_day = 1
            else:
                prev_city_idx = model.eval(city_map[day - 1]).as_long()
                prev_city = cities[prev_city_idx]
                if city != prev_city:
                    # Flight day: add previous city's stay up to day-1, then flight on day
                    if start_day <= day - 1:
                        if start_day == day - 1:
                            add_entry(f"Day {start_day}", prev_city)
                        else:
                            add_entry(f"Day {start_day}-{day - 1}", prev_city)
                    add_entry(f"Day {day}", prev_city)
                    add_entry(f"Day {day}", city)
                    current_place = city
                    start_day = day + 1 if day + 1 <= days else day
                else:
                    pass  # same city, continue
        
        # Add the last segment
        if start_day <= days:
            if start_day == days:
                add_entry(f"Day {days}", current_place)
            else:
                add_entry(f"Day {start_day}-{days}", current_place)
        
        # Post-process to merge consecutive same-city entries
        optimized_itinerary = []
        if itinerary:
            current_entry = itinerary[0]
            for entry in itinerary[1:]:
                if entry['place'] == current_entry['place']:
                    # Parse ranges
                    current_parts = current_entry['day_range'].replace('Day ', '').split('-')
                    entry_parts = entry['day_range'].replace('Day ', '').split('-')
                    current_start = int(current_parts[0])
                    current_end = int(current_parts[-1]) if len(current_parts) > 1 else int(current_parts[0])
                    entry_start = int(entry_parts[0])
                    entry_end = int(entry_parts[-1]) if len(entry_parts) > 1 else int(entry_parts[0])
                    
                    if entry_start == current_end + 1:
                        new_start = current_start
                        new_end = entry_end
                        if new_start == new_end:
                            new_range = f"Day {new_start}"
                        else:
                            new_range = f"Day {new_start}-{new_end}"
                        current_entry = {'day_range': new_range, 'place': current_entry['place']}
                    else:
                        optimized_itinerary.append(current_entry)
                        current_entry = entry
                else:
                    optimized_itinerary.append(current_entry)
                    current_entry = entry
            optimized_itinerary.append(current_entry)
        
        # Prepare the output
        output = {"itinerary": optimized_itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))