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
    
    # Adjusted fixed events to be non-overlapping
    fixed_events = {
        'Vienna': [1, 5],
        'Prague': [6, 10],
        'Split': [11, 13],
        'Riga': [14, 15],
        'Stockholm': [16, 17]
    }
    
    # Mark which days are occupied by fixed events
    occupied = [False] * 21  # index 0 unused, days 1-20
    for city, (start, end) in fixed_events.items():
        for day in range(start, end + 1):
            if day <= 20:
                occupied[day] = True

    # We'll use DFS to build the itinerary
    itinerary = []  # list of (start, end, city)
    all_cities = list(req_days.keys())
    
    # Check if a city placement is valid
    def can_place(start, end, city):
        # Check days are within bounds
        if end > 20:
            return False
        # Check if any day in [start, end] is already occupied
        for day in range(start, end + 1):
            if occupied[day]:
                return False
        return True
    
    # Mark days as occupied
    def mark_days(start, end, value):
        for day in range(start, end + 1):
            occupied[day] = value
    
    # DFS function
    def dfs(cities_left, last_city):
        # If all cities placed, check if we've used exactly 20 days
        if not cities_left:
            # Check if all days from 1 to 20 are covered
            if all(occupied[1:21]):
                return []
            return None
        
        for city in cities_left:
            # Check flight connection
            if last_city and city not in graph[last_city]:
                continue
                
            days_needed = req_days[city]
            # Try every possible start day
            for start_day in range(1, 21):
                end_day = start_day + days_needed - 1
                if can_place(start_day, end_day, city):
                    # Place this city
                    mark_days(start_day, end_day, True)
                    new_cities_left = cities_left.copy()
                    new_cities_left.remove(city)
                    # Recurse
                    result = dfs(new_cities_left, city)
                    if result is not None:
                        return [(start_day, end_day, city)] + result
                    # Backtrack
                    mark_days(start_day, end_day, False)
        return None
    
    # Place fixed events first
    fixed_cities = set()
    for city, (start, end) in fixed_events.items():
        itinerary.append((start, end, city))
        mark_days(start, end, True)
        fixed_cities.add(city)
    
    # Start DFS with remaining cities
    remaining_cities = set(all_cities) - fixed_cities
    result_itinerary = dfs(remaining_cities, None)
    
    if result_itinerary is None:
        print('No valid itinerary found.')
        return
    
    # Combine fixed and DFS itinerary
    full_itinerary = itinerary + result_itinerary
    # Sort by start day
    full_itinerary.sort(key=lambda x: x[0])
    
    # Format the itinerary for output
    itinerary_list = []
    for start, end, city in full_itinerary:
        day_range = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()