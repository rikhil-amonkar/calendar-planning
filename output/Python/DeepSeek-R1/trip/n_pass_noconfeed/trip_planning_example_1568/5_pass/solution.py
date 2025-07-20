import json
from itertools import permutations

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
    itinerary = sorted_fixed  # This will be part of the final itinerary
    
    # Mark occupied days (1-20)
    occupied = [False] * 21  # index 0 unused, days 1-20
    for city, (start, end) in fixed_events.items():
        for day in range(start, end + 1):
            if day <= 20:
                occupied[day] = True
    
    # Identify available gaps between fixed events
    gaps = []
    current_day = 1
    for start, end, city in sorted_fixed:
        if current_day < start:
            gaps.append((current_day, start - 1))
        current_day = end + 1
    if current_day <= 20:
        gaps.append((current_day, 20))
    
    # Get remaining cities
    all_cities = set(req_days.keys())
    fixed_cities = set(fixed_events.keys())
    remaining_cities = list(all_cities - fixed_cities)
    last_city = sorted_fixed[-1][2] if sorted_fixed else None
    
    # DFS to place remaining cities in gaps
    def dfs(idx, last_city, remaining):
        if idx >= len(gaps) and not remaining:
            return []
        if idx >= len(gaps):
            return None
            
        start_gap, end_gap = gaps[idx]
        gap_len = end_gap - start_gap + 1
        
        for perm in permutations(remaining):
            placements = []
            current_start = start_gap
            current_last_city = last_city
            valid_placement = True
            
            for city in perm:
                days_needed = req_days[city]
                end_place = current_start + days_needed - 1
                if end_place > end_gap:
                    valid_placement = False
                    break
                    
                # Check flight connection
                if current_last_city and city not in graph[current_last_city]:
                    valid_placement = False
                    break
                    
                # Check if days are available
                for day in range(current_start, end_place + 1):
                    if occupied[day]:
                        valid_placement = False
                        break
                if not valid_placement:
                    break
                    
                placements.append((current_start, end_place, city))
                current_last_city = city
                current_start = end_place + 1
                
            if not valid_placement:
                continue
                
            # If we haven't used the entire gap, skip this permutation
            if current_start - 1 != end_gap:
                continue
                
            # Temporarily mark days as occupied
            for (s, e, _) in placements:
                for day in range(s, e + 1):
                    occupied[day] = True
                    
            # Recurse to next gap
            new_remaining = [c for c in remaining if c not in [plc[2] for plc in placements]]
            res = dfs(idx + 1, current_last_city, new_remaining)
            if res is not None:
                return placements + res
                
            # Backtrack: unmark days
            for (s, e, _) in placements:
                for day in range(s, e + 1):
                    occupied[day] = False
                    
        return None
        
    result_remaining = dfs(0, last_city, remaining_cities)
    
    if result_remaining is None:
        print('No valid itinerary found (insufficient time or flight connections).')
        return
        
    # Combine fixed events and placed cities
    full_itinerary = itinerary + result_remaining
    full_itinerary.sort(key=lambda x: x[0])
    
    # Validate the entire itinerary
    # 1. Check flight connections
    prev_city = full_itinerary[0][2]
    for i in range(1, len(full_itinerary)):
        current_city = full_itinerary[i][2]
        if current_city not in graph[prev_city]:
            print('No valid itinerary found (flight connection error between {} and {}).'.format(prev_city, current_city))
            return
        prev_city = current_city
        
    # 2. Check for overlaps and coverage
    days_covered = [False] * 21
    itinerary_cities = set()
    for start, end, city in full_itinerary:
        itinerary_cities.add(city)
        for day in range(start, end + 1):
            if day < 1 or day > 20:
                print('No valid itinerary found (day out of range).')
                return
            if days_covered[day]:
                print('No valid itinerary found (overlapping events on day {}).'.format(day))
                return
            days_covered[day] = True
            
    # 3. Check all cities included
    if itinerary_cities != all_cities:
        print('No valid itinerary found (missing cities).')
        return
        
    # Format output
    itinerary_list = []
    for start, end, city in full_itinerary:
        day_range = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()