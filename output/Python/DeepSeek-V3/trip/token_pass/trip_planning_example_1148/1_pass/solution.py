import json

def solve_trip():
    # Cities and required days
    cities = {
        'Lisbon': 2,
        'Dubrovnik': 5,
        'Copenhagen': 5,
        'Prague': 3,
        'Tallinn': 2,
        'Stockholm': 4,
        'Split': 3,
        'Lyon': 2
    }
    
    # Direct flights (undirected)
    flights = {
        'Dubrovnik': ['Stockholm', 'Copenhagen'],
        'Stockholm': ['Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Lisbon', 'Split'],
        'Lisbon': ['Copenhagen', 'Lyon', 'Stockholm', 'Prague'],
        'Copenhagen': ['Lisbon', 'Stockholm', 'Split', 'Dubrovnik', 'Prague', 'Tallinn'],
        'Prague': ['Stockholm', 'Lyon', 'Lisbon', 'Copenhagen', 'Split', 'Tallinn'],
        'Tallinn': ['Stockholm', 'Copenhagen', 'Prague'],
        'Split': ['Copenhagen', 'Stockholm', 'Lyon', 'Prague'],
        'Lyon': ['Lisbon', 'Prague', 'Split']
    }
    
    # Fixed events: day -> city
    fixed_events = {}
    # Tallinn day 1-2
    fixed_events[1] = 'Tallinn'
    fixed_events[2] = 'Tallinn'
    # Lisbon day 4-5
    fixed_events[4] = 'Lisbon'
    fixed_events[5] = 'Lisbon'
    # Stockholm day 13-16
    for d in range(13, 17):
        fixed_events[d] = 'Stockholm'
    # Lyon day 18-19
    fixed_events[18] = 'Lyon'
    fixed_events[19] = 'Lyon'
    
    total_days = 19
    schedule = [None] * (total_days + 1)  # index 1..19
    for day, city in fixed_events.items():
        schedule[day] = city
    
    # Count days assigned so far
    used_days = {city: 0 for city in cities}
    for city in schedule[1:]:
        if city:
            used_days[city] += 1
    
    # Check if any city exceeds required days already
    for city, req in cities.items():
        if used_days[city] > req:
            return None  # impossible
    
    # Backtracking function
    def backtrack(day):
        if day > total_days:
            # All days filled, check totals match
            for city, req in cities.items():
                if used_days[city] != req:
                    return None
            return schedule[1:]  # return list of cities per day
        
        # If this day is fixed, move to next
        if schedule[day] is not None:
            return backtrack(day + 1)
        
        # Try each city
        for city in cities:
            # Check if we can still use this city
            if used_days[city] >= cities[city]:
                continue
            
            # Check connectivity with previous day
            if day > 1:
                prev_city = schedule[day - 1]
                if prev_city != city and city not in flights[prev_city]:
                    continue
            
            # Assign
            schedule[day] = city
            used_days[city] += 1
            
            # Recurse
            res = backtrack(day + 1)
            if res is not None:
                return res
            
            # Undo
            schedule[day] = None
            used_days[city] -= 1
        
        return None
    
    final_schedule = backtrack(1)
    if final_schedule is None:
        return {"itinerary": []}
    
    # Convert to day ranges
    itinerary = []
    start = 1
    current_city = final_schedule[0]
    for d in range(2, total_days + 1):
        if final_schedule[d - 1] != current_city:
            itinerary.append({
                "day_range": f"Day {start}-{d - 1}",
                "place": current_city
            })
            start = d
            current_city = final_schedule[d - 1]
    # Add last segment
    itinerary.append({
        "day_range": f"Day {start}-{total_days}",
        "place": current_city
    })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip()
    print(json.dumps(result, indent=2))