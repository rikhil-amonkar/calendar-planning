from z3 import *
import json

def solve_itinerary():
    # Cities involved with correct spellings
    cities = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    
    # Direct flight connections (bidirectional)
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
    
    # Create a Z3 array where each day is mapped to a city
    city_map = Array('city_map', Day, IntSort())
    
    # Assign each city to an integer ID
    city_ids = {city: idx for idx, city in enumerate(cities)}
    
    # Constraints for each day's city assignment
    for day in range(1, days + 1):
        solver.add(And(city_map[day] >= 0, city_map[day] < len(cities)))
    
    # Fixed date constraints
    # Venice must be visited between days 22-26
    for day in range(22, 27):
        solver.add(city_map[day] == city_ids["Venice"])
    
    # Frankfurt must be visited between days 12-16
    for day in range(12, 17):
        solver.add(city_map[day] == city_ids["Frankfurt"])
    
    # Tallinn must be visited between days 8-12
    for day in range(8, 13):
        solver.add(city_map[day] == city_ids["Tallinn"])
    
    # Count days in each city
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
    
    # Flight constraints
    for day in range(1, days):
        current_city = city_map[day]
        next_city = city_map[day + 1]
        # If changing cities, must have direct flight
        solver.add(Implies(current_city != next_city, 
                        Or([And(current_city == city_ids[c1], next_city == city_ids[c2]) 
                           for c1 in direct_flights for c2 in direct_flights[c1]])))
    
    # Additional constraints to prevent impossible transitions
    # Ensure we don't have single-day stays that would require impossible flights
    for city in cities:
        solver.add(Implies(Or([city_map[day] == city_ids[city] for day in range(1, days + 1)]),
                         Or([city_map[day] == city_ids[city] for day in range(1, days + 1)])))
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        # Extract itinerary
        itinerary = []
        current_place = None
        start_day = 1
        
        def add_entry(day_range, place):
            itinerary.append({"day_range": day_range, "place": place})
        
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
                    if start_day <= day - 1:
                        if start_day == day - 1:
                            add_entry(f"Day {start_day}", prev_city)
                        else:
                            add_entry(f"Day {start_day}-{day - 1}", prev_city)
                    add_entry(f"Day {day}", prev_city)
                    add_entry(f"Day {day}", city)
                    current_place = city
                    start_day = day + 1 if day + 1 <= days else day
        
        if start_day <= days:
            if start_day == days:
                add_entry(f"Day {days}", current_place)
            else:
                add_entry(f"Day {start_day}-{days}", current_place)
        
        # Optimize itinerary by merging consecutive entries
        optimized = []
        if itinerary:
            current = itinerary[0]
            for entry in itinerary[1:]:
                if entry['place'] == current['place']:
                    # Parse day ranges
                    def parse_days(s):
                        parts = s.replace('Day ', '').split('-')
                        return int(parts[0]), int(parts[-1])
                    start1, end1 = parse_days(current['day_range'])
                    start2, end2 = parse_days(entry['day_range'])
                    if end1 + 1 == start2:
                        current['day_range'] = f"Day {start1}-{end2}"
                    else:
                        optimized.append(current)
                        current = entry
                else:
                    optimized.append(current)
                    current = entry
            optimized.append(current)
        
        return {"itinerary": optimized}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
print(json.dumps(result, indent=2))