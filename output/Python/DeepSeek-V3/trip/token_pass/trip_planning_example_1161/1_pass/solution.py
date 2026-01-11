import json

def solve():
    # Cities and required days
    cities = {
        'Mykonos': 4,
        'Krakow': 5,
        'Vilnius': 2,
        'Helsinki': 2,
        'Dubrovnik': 3,
        'Oslo': 2,
        'Madrid': 5,
        'Paris': 2
    }
    
    # Direct flights (undirected)
    direct_flights = {
        'Oslo': ['Krakow', 'Paris', 'Madrid', 'Helsinki', 'Dubrovnik', 'Vilnius'],
        'Krakow': ['Oslo', 'Paris', 'Helsinki', 'Vilnius'],
        'Paris': ['Oslo', 'Madrid', 'Krakow', 'Helsinki', 'Vilnius'],
        'Madrid': ['Paris', 'Oslo', 'Dubrovnik', 'Helsinki', 'Mykonos'],
        'Helsinki': ['Vilnius', 'Oslo', 'Krakow', 'Dubrovnik', 'Paris', 'Madrid'],
        'Dubrovnik': ['Helsinki', 'Madrid', 'Oslo'],
        'Vilnius': ['Helsinki', 'Oslo', 'Krakow', 'Paris'],
        'Mykonos': ['Madrid']
    }
    
    # Fixed events
    # Dubrovnik days 2-4 inclusive
    # Mykonos days 15-18 inclusive
    fixed = {
        2: 'Dubrovnik',
        3: 'Dubrovnik',
        4: 'Dubrovnik',
        15: 'Mykonos',
        16: 'Mykonos',
        17: 'Mykonos',
        18: 'Mykonos'
    }
    
    total_days = 18
    itinerary = []  # list of (start_day, end_day, city)
    used_days = {city: 0 for city in cities}
    
    # Helper to check if we can travel from city A to city B
    def can_travel(a, b):
        if a is None or b is None:
            return True
        return b in direct_flights[a]
    
    # Backtracking search
    def backtrack(day, current_city, path):
        if day > total_days:
            # Check if all cities have required days
            for city, req in cities.items():
                if used_days[city] < req:
                    return None
            return path[:]
        
        # If this day is fixed to a city
        if day in fixed:
            fixed_city = fixed[day]
            if current_city == fixed_city:
                # Stay here
                used_days[fixed_city] += 1
                # Extend last stay in path
                if path and path[-1][2] == fixed_city:
                    path[-1] = (path[-1][0], day, fixed_city)
                else:
                    path.append((day, day, fixed_city))
                res = backtrack(day + 1, fixed_city, path)
                if res:
                    return res
                # Undo
                if path[-1][0] == day and path[-1][1] == day:
                    path.pop()
                else:
                    path[-1] = (path[-1][0], path[-1][1] - 1, fixed_city)
                used_days[fixed_city] -= 1
                return None
            else:
                # Need to travel to fixed_city
                if not can_travel(current_city, fixed_city):
                    return None
                # Travel day: count for both cities
                used_days[current_city] += 1
                used_days[fixed_city] += 1
                # End previous stay at day
                if path and path[-1][2] == current_city:
                    path[-1] = (path[-1][0], day, current_city)
                else:
                    path.append((day, day, current_city))
                # Start new stay at fixed_city
                path.append((day, day, fixed_city))
                res = backtrack(day + 1, fixed_city, path)
                if res:
                    return res
                # Undo
                path.pop()
                if path[-1][0] == day and path[-1][1] == day:
                    path.pop()
                else:
                    path[-1] = (path[-1][0], path[-1][1] - 1, current_city)
                used_days[current_city] -= 1
                used_days[fixed_city] -= 1
                return None
        
        # Try staying in current city
        if current_city is not None:
            used_days[current_city] += 1
            if path and path[-1][2] == current_city:
                old_end = path[-1][1]
                path[-1] = (path[-1][0], day, current_city)
                res = backtrack(day + 1, current_city, path)
                if res:
                    return res
                path[-1] = (path[-1][0], old_end, current_city)
            else:
                path.append((day, day, current_city))
                res = backtrack(day + 1, current_city, path)
                if res:
                    return res
                path.pop()
            used_days[current_city] -= 1
        
        # Try traveling to another city
        for next_city in cities:
            if next_city == current_city:
                continue
            if not can_travel(current_city, next_city):
                continue
            # Travel consumes day for both cities
            if current_city is not None:
                used_days[current_city] += 1
            used_days[next_city] += 1
            
            # End previous stay
            if current_city is not None:
                if path and path[-1][2] == current_city:
                    path[-1] = (path[-1][0], day, current_city)
                else:
                    path.append((day, day, current_city))
            # Start new stay
            path.append((day, day, next_city))
            
            res = backtrack(day + 1, next_city, path)
            if res:
                return res
            
            # Undo
            path.pop()
            if current_city is not None:
                if path[-1][0] == day and path[-1][1] == day:
                    path.pop()
                else:
                    path[-1] = (path[-1][0], path[-1][1] - 1, current_city)
            
            if current_city is not None:
                used_days[current_city] -= 1
            used_days[next_city] -= 1
        
        return None
    
    # Start with Oslo on day 1 (to satisfy Oslo day 1-2 requirement)
    used_days['Oslo'] = 1
    path = [(1, 1, 'Oslo')]
    solution = backtrack(2, 'Oslo', path)
    
    if not solution:
        return {"itinerary": []}
    
    # Convert to required JSON format
    itinerary_json = []
    for start, end, city in solution:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary_json.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary_json}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))