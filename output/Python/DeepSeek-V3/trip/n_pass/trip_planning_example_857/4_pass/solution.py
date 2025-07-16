import json

def find_itinerary():
    # Cities and their required days
    cities = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2
    }
    
    # Direct flights
    direct_flights = {
        "Hamburg": ["Frankfurt", "Porto", "Geneva", "Manchester"],
        "Frankfurt": ["Hamburg", "Geneva", "Porto", "Naples", "Manchester"],
        "Geneva": ["Hamburg", "Mykonos", "Frankfurt", "Porto", "Manchester", "Naples"],
        "Mykonos": ["Geneva", "Naples"],
        "Naples": ["Mykonos", "Manchester", "Frankfurt", "Geneva"],
        "Porto": ["Hamburg", "Frankfurt", "Geneva", "Manchester"],
        "Manchester": ["Geneva", "Naples", "Frankfurt", "Porto", "Hamburg"]
    }
    
    # Constraints
    constraints = {
        "Mykonos": (10, 12),  # Must be visited between days 10-12
        "Manchester": (15, 18),  # Must be visited between days 15-18
        "Frankfurt": (5, 6)  # Must be visited between days 5-6
    }
    
    # We'll build the itinerary day by day
    itinerary = []
    used_cities = set()
    total_days = 0
    
    def backtrack(current_day):
        nonlocal total_days
        
        # Check if we've used all cities and total days is exactly 18
        if len(used_cities) == len(cities) and total_days == 18:
            return True
        
        # Try each city that hasn't been used yet
        for city in cities:
            if city in used_cities:
                continue
                
            days_needed = cities[city]
            start_day = current_day
            end_day = current_day + days_needed - 1
            
            # Check if this city has day constraints
            if city in constraints:
                constraint_start, constraint_end = constraints[city]
                # Check if we can fit the city in its required window
                if not (constraint_start <= start_day and end_day <= constraint_end):
                    # Try to adjust to fit in the window
                    if (constraint_end - constraint_start + 1) < days_needed:
                        continue  # Can't fit
                    start_day = constraint_start
                    end_day = start_day + days_needed - 1
                    if end_day > constraint_end:
                        continue  # Still can't fit
            
            # Check if this would exceed total days
            if end_day > 18:
                continue
                
            # Check flight connection with previous city if not first city
            if itinerary:
                prev_city = itinerary[-1]["place"]
                if city not in direct_flights.get(prev_city, []):
                    continue
            
            # Add to itinerary
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
            used_cities.add(city)
            total_days += days_needed
            
            # Recurse with next available day
            if backtrack(end_day + 1):
                return True
                
            # Backtrack
            itinerary.pop()
            used_cities.remove(city)
            total_days -= days_needed
        
        return False
    
    # Start the backtracking
    if backtrack(1):
        # Verify total days
        calculated_days = 0
        for item in itinerary:
            start, end = map(int, item["day_range"].split(" ")[1].split("-"))
            calculated_days += (end - start + 1)
        
        if calculated_days == 18:
            return {"itinerary": itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))