import json
from itertools import permutations

def find_itinerary():
    # City stay requirements
    stays = {
        'Geneva': 4,
        'Munich': 7,
        'Bucharest': 2,
        'Valencia': 6,
        'Stuttgart': 2
    }
    
    # Direct flights graph
    flights = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Bucharest': ['Munich', 'Valencia'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Stuttgart': ['Valencia']
    }
    
    cities = list(stays.keys())
    
    # Try all permutations of the 5 cities
    for perm in permutations(cities):
        # Check direct flights between consecutive cities
        valid_route = True
        for i in range(len(perm) - 1):
            if perm[i + 1] not in flights[perm[i]]:
                valid_route = False
                break
        if not valid_route:
            continue
        
        # Now calculate day ranges
        # We have 4 travel days (overlap days)
        # Start day 1 in first city
        day_ranges = []
        current_day = 1
        for idx, city in enumerate(perm):
            stay_duration = stays[city]
            if idx == 0:
                # First city: start at day 1, stay full duration
                start_day = current_day
                end_day = start_day + stay_duration - 1
                day_ranges.append((start_day, end_day, city))
                current_day = end_day  # last day is also travel day to next
            elif idx == len(perm) - 1:
                # Last city: start at current_day (overlap with previous city)
                start_day = current_day
                end_day = start_day + stay_duration - 1
                day_ranges.append((start_day, end_day, city))
                # Final day should be total 17
                if end_day != 17:
                    valid_route = False
                    break
            else:
                # Middle city: start at current_day (overlap)
                start_day = current_day
                end_day = start_day + stay_duration - 1
                day_ranges.append((start_day, end_day, city))
                current_day = end_day
        
        if not valid_route:
            continue
        
        # Check Geneva constraint: must be between day 1 and 4 inclusive in calendar
        geneva_range = next(r for r in day_ranges if r[2] == 'Geneva')
        if not (geneva_range[0] <= 4 and geneva_range[1] >= 1):
            continue
        
        # Check Munich constraint: must be between day 4 and 10 inclusive in calendar
        munich_range = next(r for r in day_ranges if r[2] == 'Munich')
        if not (munich_range[0] <= 10 and munich_range[1] >= 4):
            continue
        
        # Check all cities' total days match requirements
        day_counts = {city: 0 for city in cities}
        for start, end, city in day_ranges:
            day_counts[city] += (end - start + 1)
        if all(day_counts[city] == stays[city] for city in cities):
            # Valid itinerary found
            itinerary = []
            for start, end, city in day_ranges:
                if start == end:
                    day_str = f"Day {start}"
                else:
                    day_str = f"Day {start}-{end}"
                itinerary.append({"day_range": day_str, "place": city})
            return itinerary
    
    return None

def main():
    itinerary = find_itinerary()
    if itinerary:
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()