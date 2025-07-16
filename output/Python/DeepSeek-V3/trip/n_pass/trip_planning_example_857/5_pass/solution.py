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
            
            # Check if this city has day constraints
            if city in constraints:
                constraint_start, constraint_end = constraints[city]
                # Must fit entirely within the constraint window
                if (constraint_end - constraint_start + 1) < days_needed:
                    continue  # Can't fit
                start_day = constraint_start
                end_day = start_day + days_needed - 1
            else:
                # No constraints, try to place it as early as possible
                start_day = current_day
                end_day = start_day + days_needed - 1
            
            # Check if this would exceed total days
            if end_day > 18:
                continue
                
            # Check if this overlaps with any existing itinerary items
            overlap = False
            for item in itinerary:
                existing_start = int(item["day_range"].split(" ")[1].split("-")[0])
                existing_end = int(item["day_range"].split(" ")[1].split("-")[1])
                if not (end_day < existing_start or start_day > existing_end):
                    overlap = True
                    break
            if overlap:
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
            
            # Determine next available day
            next_day = 1
            while next_day <= 18:
                occupied = False
                for item in itinerary:
                    existing_start = int(item["day_range"].split(" ")[1].split("-")[0])
                    existing_end = int(item["day_range"].split(" ")[1].split("-")[1])
                    if existing_start <= next_day <= existing_end:
                        occupied = True
                        next_day = existing_end + 1
                        break
                if not occupied:
                    break
            
            # Recurse
            if backtrack(next_day):
                return True
                
            # Backtrack
            itinerary.pop()
            used_cities.remove(city)
            total_days -= days_needed
        
        return False
    
    # Start the backtracking
    if backtrack(1):
        # Verify all constraints are met
        valid = True
        for city, (start_con, end_con) in constraints.items():
            found = False
            for item in itinerary:
                if item["place"] == city:
                    start_day = int(item["day_range"].split(" ")[1].split("-")[0])
                    end_day = int(item["day_range"].split(" ")[1].split("-")[1])
                    if not (start_con <= start_day and end_day <= end_con):
                        valid = False
                    found = True
                    break
            if not found:
                valid = False
        
        if valid and sum(cities.values()) == 18:
            return {"itinerary": itinerary}
    
    return {"itinerary": []}

# Execute and print the result
result = find_itinerary()
print(json.dumps(result, indent=2))