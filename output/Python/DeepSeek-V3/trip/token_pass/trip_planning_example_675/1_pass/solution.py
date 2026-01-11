import json

def solve():
    # Direct flights graph
    flights = {
        'Munich': ['Porto', 'Krakow', 'Milan', 'Dubrovnik', 'Split'],
        'Porto': ['Munich', 'Milan'],
        'Split': ['Milan', 'Krakow', 'Munich'],
        'Milan': ['Split', 'Porto', 'Munich', 'Krakow'],
        'Krakow': ['Munich', 'Split', 'Milan'],
        'Dubrovnik': ['Munich']
    }
    
    # Required days per city
    req_days = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    
    total_days = 16
    fixed = {}
    # Day 4-8 Munich
    for d in range(4, 9):
        fixed[d] = 'Munich'
    # Day 8-9 Krakow (overwrites day 8? No, day 8 must be both Munich and Krakow if travel)
    # But in day assignment, day 8 can only be one city. So we must allow day 8 to be either Munich or Krakow
    # but ensure both get their required days including day 8.
    # Actually: day 8 is counted for both if travel. So in calendar, day 8 is assigned to one city,
    # but the other city also gets +1 day if it's a travel day. We'll handle via counting later.
    # Let's just fix day 9 = Krakow.
    fixed[9] = 'Krakow'
    # Day 11-13 Milan
    for d in range(11, 14):
        fixed[d] = 'Milan'
    
    # Backtracking search
    def backtrack(day, assignment, counts, travel_days, last_city):
        if day > total_days:
            # Check if all required days met
            for city in req_days:
                if counts.get(city, 0) != req_days[city]:
                    return None
            # Check travel days = 5
            if travel_days != 5:
                return None
            return assignment[:]
        
        # If fixed day, only that city allowed
        if day in fixed:
            city = fixed[day]
            # Check flight connectivity
            if last_city and last_city != city and city not in flights[last_city]:
                return None
            new_travel = 1 if last_city and last_city != city else 0
            counts[city] = counts.get(city, 0) + 1
            assignment.append(city)
            res = backtrack(day+1, assignment, counts, travel_days + new_travel, city)
            if res:
                return res
            assignment.pop()
            counts[city] -= 1
            return None
        
        # Try all cities
        for city in req_days.keys():
            # Check if already reached required days
            if counts.get(city, 0) >= req_days[city]:
                continue
            # Check flight connectivity
            if last_city and last_city != city and city not in flights[last_city]:
                continue
            new_travel = 1 if last_city and last_city != city else 0
            counts[city] = counts.get(city, 0) + 1
            assignment.append(city)
            res = backtrack(day+1, assignment, counts, travel_days + new_travel, city)
            if res:
                return res
            assignment.pop()
            counts[city] -= 1
        return None
    
    assignment = backtrack(1, [], {}, 0, None)
    
    if not assignment:
        return {"itinerary": []}
    
    # Convert to day ranges
    itinerary = []
    start = 1
    current_city = assignment[0]
    for d in range(2, total_days + 1):
        if assignment[d-1] != current_city:
            end = d - 1
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": current_city})
            start = d
            current_city = assignment[d-1]
    # Last segment
    end = total_days
    if start == end:
        day_range = f"Day {start}"
    else:
        day_range = f"Day {start}-{end}"
    itinerary.append({"day_range": day_range, "place": current_city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))