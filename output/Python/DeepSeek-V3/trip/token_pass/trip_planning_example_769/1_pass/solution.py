import json
from itertools import permutations

def solve():
    # Cities and required total days in each
    required_days = {
        'Porto': 5,
        'Prague': 4,
        'Reykjavik': 4,
        'Santorini': 2,
        'Amsterdam': 2,
        'Munich': 4
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('Porto', 'Amsterdam'),
        ('Munich', 'Amsterdam'),
        ('Reykjavik', 'Amsterdam'),
        ('Munich', 'Porto'),
        ('Prague', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Amsterdam', 'Santorini'),
        ('Prague', 'Amsterdam'),
        ('Prague', 'Munich')
    ]
    # Make lookup
    connected = {city: set() for city in required_days}
    for a, b in direct_flights:
        connected[a].add(b)
        connected[b].add(a)
    
    total_days = 16
    
    # Fixed events: (city, start_day, end_day inclusive)
    fixed_events = [
        ('Reykjavik', 4, 7),   # wedding
        ('Amsterdam', 14, 15), # conference
        ('Munich', 7, 10)      # friend visit (at least 1 day here)
    ]
    
    # Generate all permutations of the 6 cities
    cities = list(required_days.keys())
    
    for perm in permutations(cities):
        # We'll try to assign day ranges to each city in this order
        # Start day of first city is 1
        # When moving from city A to B, travel day is last day of A and first day of B
        # So if city A ends day X, city B starts day X (same day travel)
        
        # We need to allocate days to meet required_days
        # Let's brute force split points (days when we switch cities)
        # There are 5 switches for 6 cities
        
        # We'll search over possible end days for each city
        # end_day[i] = last day in city i (1-based)
        # start_day[i] = first day in city i
        # start_day[0] = 1
        # start_day[i] = end_day[i-1] for i>0 (travel day same as previous end)
        # end_day[5] = 16
        # Days in city i = end_day[i] - start_day[i] + 1
        # But travel day counts for both cities, so total sum of days_in_city can be >16
        
        # Let's brute force end_day for first 5 cities (last city ends at 16)
        # end_day values are between 1 and 16, strictly increasing
        
        # Pre-check: fixed events must be in correct city in perm
        # Map city to its index in perm
        city_index = {city: idx for idx, city in enumerate(perm)}
        
        # Check fixed events possible in this permutation:
        ok = True
        for city, start, end in fixed_events:
            idx = city_index[city]
            # This city's range must include [start, end]
            # We don't know exact range yet, but we can check ordering:
            # The city must not be before a city that must come after it in time? 
            # Actually, we can't check without ranges, so skip for now.
            pass
        if not ok:
            continue
        
        # Try all possible end_day for first 5 cities
        from itertools import combinations
        
        # Choose 5 split points from 2..16
        for splits in combinations(range(2, 17), 5):
            splits = sorted(splits)
            if splits[-1] >= 16:
                continue
            end_days = list(splits) + [16]
            start_days = [1] + list(splits)
            
            # Now compute days in each city
            days_in_city = []
            for i in range(6):
                days = end_days[i] - start_days[i] + 1
                days_in_city.append(days)
            
            # Check required_days matches
            req_match = all(days_in_city[i] == required_days[perm[i]] for i in range(6))
            if not req_match:
                continue
            
            # Check direct flights between consecutive cities
            flight_ok = True
            for i in range(5):
                if perm[i+1] not in connected[perm[i]]:
                    flight_ok = False
                    break
            if not flight_ok:
                continue
            
            # Check fixed events
            event_ok = True
            for city, start, end in fixed_events:
                idx = city_index[city]
                if not (start_days[idx] <= start and end_days[idx] >= end):
                    event_ok = False
                    break
            if not event_ok:
                continue
            
            # Also check Munich friend visit: at least 1 day between 7 and 10
            munich_idx = city_index['Munich']
            munich_start = start_days[munich_idx]
            munich_end = end_days[munich_idx]
            # Overlap with 7-10
            if munich_end < 7 or munich_start > 10:
                event_ok = False
            if not event_ok:
                continue
            
            # Found valid itinerary
            itinerary = []
            for i in range(6):
                if start_days[i] == end_days[i]:
                    day_str = f"Day {start_days[i]}"
                else:
                    day_str = f"Day {start_days[i]}-{end_days[i]}"
                itinerary.append({
                    "day_range": day_str,
                    "place": perm[i]
                })
            
            # Verify total distinct days = 16
            distinct_days_set = set()
            for i in range(6):
                for d in range(start_days[i], end_days[i] + 1):
                    distinct_days_set.add(d)
            if len(distinct_days_set) != 16:
                continue  # shouldn't happen given constraints
            
            return itinerary
    
    return None

def main():
    itinerary = solve()
    if itinerary is None:
        print('{"error": "No valid itinerary found"}')
    else:
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()