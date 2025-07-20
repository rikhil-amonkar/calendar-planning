import json

def main():
    # Define the graph of direct flights (bidirectional)
    graph = {
        'Riga': ['Stockholm', 'Istanbul', 'Amsterdam', 'Brussels', 'Munich', 'Prague'],
        'Stockholm': ['Riga', 'Brussels', 'Split', 'Amsterdam', 'Vienna', 'Istanbul', 'Prague', 'Munich'],
        'Brussels': ['Stockholm', 'Vienna', 'Munich', 'Prague', 'Istanbul', 'Riga', 'Seville'],
        'Istanbul': ['Munich', 'Riga', 'Vienna', 'Stockholm', 'Amsterdam', 'Brussels'],
        'Prague': ['Split', 'Munich', 'Amsterdam', 'Brussels', 'Istanbul', 'Riga', 'Stockholm', 'Vienna'],
        'Munich': ['Istanbul', 'Amsterdam', 'Brussels', 'Prague', 'Split', 'Stockholm', 'Seville', 'Riga'],
        'Split': ['Prague', 'Munich', 'Amsterdam', 'Stockholm', 'Vienna'],
        'Amsterdam': ['Munich', 'Split', 'Stockholm', 'Riga', 'Seville', 'Istanbul', 'Vienna'],
        'Vienna': ['Brussels', 'Riga', 'Stockholm', 'Istanbul', 'Seville', 'Prague', 'Split', 'Amsterdam', 'Munich'],
        'Seville': ['Brussels', 'Amsterdam', 'Vienna', 'Munich']
    }
    
    # Define the required days per city
    req_days = {
        'Prague': 5,
        'Brussels': 2,
        'Riga': 2,
        'Munich': 2,
        'Seville': 3,
        'Stockholm': 2,
        'Istanbul': 2,
        'Amsterdam': 3,
        'Vienna': 5,
        'Split': 3
    }
    
    # Fixed events (non-overlapping and already scheduled)
    fixed_events = {
        'Vienna': [1, 5],
        'Prague': [6, 10],
        'Split': [11, 13],
        'Riga': [14, 15],
        'Stockholm': [16, 17]
    }
    
    # Sort fixed events by start day
    fixed_event_list = []
    for city, (start, end) in fixed_events.items():
        fixed_event_list.append((start, end, city))
    sorted_fixed = sorted(fixed_event_list, key=lambda x: x[0])
    
    # Validate flight connections between consecutive fixed events
    for i in range(len(sorted_fixed) - 1):
        city1 = sorted_fixed[i][2]
        city2 = sorted_fixed[i+1][2]
        if city2 not in graph[city1]:
            print('No valid itinerary found (fixed events flight connection error).')
            return
    
    # Mark occupied days (1-20)
    occupied = [False] * 21  # index 0 unused, days 1-20
    for city, (start, end) in fixed_events.items():
        for day in range(start, end + 1):
            if day <= 20:
                occupied[day] = True
    
    # Identify available gaps
    gaps = []
    current_day = 1
    for start, end, city in sorted_fixed:
        if current_day < start:
            gaps.append((current_day, start - 1))
        current_day = end + 1
    if current_day <= 20:
        gaps.append((current_day, 20))
    
    # Prepare itinerary with fixed events
    itinerary = sorted_fixed  # (start, end, city)
    last_city = sorted_fixed[-1][2] if sorted_fixed else None
    
    # Get remaining cities
    all_cities = set(req_days.keys())
    fixed_cities = {city for _, _, city in sorted_fixed}
    remaining_cities = list(all_cities - fixed_cities)
    
    # DFS to place remaining cities in gaps
    def dfs(idx, last_city, remaining):
        if idx >= len(gaps) and not remaining:
            return []
        if idx >= len(gaps):
            return None
            
        start_gap, end_gap = gaps[idx]
        gap_len = end_gap - start_gap + 1
        
        for perm in permutations(remaining):
            # Try to place cities in current gap
            temp_remaining = list(perm)
            placements = []
            current_start = start_gap
            valid = True
            
            for city in temp_remaining:
                days_needed = req_days[city]
                if current_start + days_needed - 1 > end_gap:
                    valid = False
                    break
                # Check flight connection
                if last_city and city not in graph[last_city]:
                    valid = False
                    break
                # Place city
                placements.append((current_start, current_start + days_needed - 1, city))
                # Update last city and next start
                last_city = city
                current_start += days_needed
            
            if not valid or current_start <= end_gap:
                continue
                
            # Check if this placement uses the entire gap
            if current_start - 1 != end_gap:
                continue
                
            # Check if placements are valid
            for (s, e, _) in placements:
                for day in range(s, e+1):
                    if occupied[day]:
                        valid = False
                        break
                if not valid:
                    break
                    
            if not valid:
                continue
                
            # Mark days for placements
            for (s, e, _) in placements:
                for day in range(s, e+1):
                    occupied[day] = True
                    
            # Recurse to next gap
            new_remaining = [c for c in remaining if c not in [city for _, _, city in placements]]
            res = dfs(idx+1, last_city, new_remaining)
            if res is not None:
                return placements + res
                
            # Backtrack
            for (s, e, _) in placements:
                for day in range(s, e+1):
                    occupied[day] = False
                    
        return None
        
    from itertools import permutations
    result_remaining = dfs(0, last_city, remaining_cities)
    
    if result_remaining is None:
        print('No valid itinerary found.')
        return
        
    # Combine all parts
    full_itinerary = itinerary + result_remaining
    full_itinerary.sort(key=lambda x: x[0])
    
    # Format output
    itinerary_list = []
    for start, end, city in full_itinerary:
        day_range = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()