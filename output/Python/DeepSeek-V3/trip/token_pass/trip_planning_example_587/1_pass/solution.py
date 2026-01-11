import json
from itertools import permutations

def solve():
    cities = ["Manchester", "Venice", "Istanbul", "Krakow", "Lyon"]
    required_days = {
        "Manchester": 3,
        "Venice": 7,
        "Istanbul": 7,
        "Krakow": 6,
        "Lyon": 2
    }
    
    # Direct flights graph
    direct_flights = {
        "Manchester": ["Venice", "Istanbul", "Krakow"],
        "Venice": ["Manchester", "Istanbul", "Lyon"],
        "Istanbul": ["Manchester", "Venice", "Krakow", "Lyon"],
        "Krakow": ["Istanbul", "Manchester"],
        "Lyon": ["Venice", "Istanbul"]
    }
    
    total_days = 21
    
    # Fixed constraints:
    # Manchester days 1-3 (day 3 also Venice)
    # Venice days 3-9 (day 9 also next city)
    # So initial sequence: Manchester, Venice
    
    # Remaining cities to visit after Venice: Istanbul, Krakow, Lyon
    remaining_cities = ["Istanbul", "Krakow", "Lyon"]
    
    best_sequence = None
    best_schedule = None
    
    # Try all permutations of remaining cities after Venice
    for perm in permutations(remaining_cities):
        sequence = ["Manchester", "Venice"] + list(perm)
        # Check direct flight connections
        valid = True
        for i in range(len(sequence) - 1):
            if sequence[i+1] not in direct_flights[sequence[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Now assign days
        # Manchester: days 1-3 (3 days)
        # Venice: days 3-9 (7 days)
        # So day 3 is both Manchester and Venice
        # Day 9 is both Venice and next city (perm[0])
        
        # We need to allocate days for remaining cities
        # Days already allocated: day 1-9 accounted for Manchester and Venice
        # Remaining calendar days: day 10 to day 21 (12 days)
        # But travel overlaps can help
        
        # Let's model it:
        # Start day index at 1
        # For each city in sequence, we spend required_days[city] days there
        # but travel day is shared with next city
        
        # Let's brute force day allocation
        # We know first two cities:
        # Manchester: day 1 to day 3 (3 days)
        # Venice: day 3 to day X, where X = 3 + 7 - 1 = 9 (because day 3 counted for both)
        # So Venice ends day 9.
        
        # Now for remaining cities, we start at day 9 (shared with Venice)
        # and allocate required days with overlaps
        
        # Let's try greedy: each city starts on the last day of previous city
        schedule = []
        day_start = 1
        for idx, city in enumerate(sequence):
            needed = required_days[city]
            if idx == 0:
                # Manchester
                day_end = day_start + needed - 1
                schedule.append((city, day_start, day_end))
                day_start = day_end  # next city starts same day
            elif idx == 1:
                # Venice
                day_end = day_start + needed - 1
                schedule.append((city, day_start, day_end))
                day_start = day_end
            else:
                # Remaining cities
                day_end = day_start + needed - 1
                schedule.append((city, day_start, day_end))
                day_start = day_end
        
        # Check if day_end for last city is total_days
        if schedule[-1][2] == total_days:
            # Also check all required days met
            days_spent = {}
            for city, start, end in schedule:
                days_spent[city] = days_spent.get(city, 0) + (end - start + 1)
            # Adjust for overlaps: actually our schedule already counts overlaps correctly
            # because start day is same as previous end day
            # Let's verify:
            ok = True
            for city in cities:
                total = 0
                for c, s, e in schedule:
                    if c == city:
                        total += (e - s + 1)
                if total != required_days[city]:
                    ok = False
                    break
            if ok:
                best_sequence = sequence
                best_schedule = schedule
                break
    
    # Convert to required JSON format
    itinerary = []
    for city, start, end in best_schedule:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))