import json
from itertools import permutations

def solve():
    # Cities and required days
    cities = {
        "Paris": 2,
        "Barcelona": 5,
        "Amsterdam": 2,
        "Tallinn": 2,
        "Vilnius": 3,
        "Warsaw": 4,
        "Venice": 3,
        "Florence": 5,
        "Hamburg": 4,
        "Salzburg": 4
    }
    
    # Fixed date ranges (inclusive start, inclusive end)
    fixed = {
        "Paris": (1, 2),
        "Barcelona": (2, 6),
        "Tallinn": (11, 12),
        "Hamburg": (19, 22),
        "Salzburg": (22, 25)
    }
    
    # Direct flights adjacency list
    direct_flights = {
        "Paris": ["Venice", "Hamburg", "Vilnius", "Amsterdam", "Florence", "Warsaw", "Tallinn", "Barcelona"],
        "Barcelona": ["Amsterdam", "Warsaw", "Hamburg", "Florence", "Venice", "Tallinn", "Paris"],
        "Amsterdam": ["Barcelona", "Warsaw", "Vilnius", "Hamburg", "Florence", "Tallinn", "Venice"],
        "Tallinn": ["Barcelona", "Warsaw", "Vilnius", "Amsterdam", "Paris"],
        "Vilnius": ["Amsterdam", "Warsaw", "Paris", "Tallinn"],
        "Warsaw": ["Amsterdam", "Barcelona", "Venice", "Vilnius", "Hamburg", "Tallinn", "Paris"],
        "Venice": ["Paris", "Warsaw", "Barcelona", "Hamburg", "Amsterdam"],
        "Florence": ["Barcelona", "Paris", "Amsterdam"],
        "Hamburg": ["Amsterdam", "Barcelona", "Paris", "Venice", "Warsaw", "Salzburg"],
        "Salzburg": ["Hamburg"]
    }
    
    # All cities list
    all_cities = list(cities.keys())
    
    # Remove fixed cities from permutation search, they are pre-placed
    flexible = [c for c in all_cities if c not in fixed]
    
    # Pre-place fixed cities in schedule
    schedule = {}
    for day in range(1, 26):
        schedule[day] = []
    
    for city, (start, end) in fixed.items():
        for day in range(start, end + 1):
            schedule[day].append(city)
    
    # Helper to check if two cities are connected by direct flight
    def connected(a, b):
        return b in direct_flights[a]
    
    # Backtracking search
    def backtrack(index, perm, day_pointer, remaining_days):
        if index == len(perm):
            # Check if all days are filled or overlapping is fine
            # Actually we just need all cities' required days satisfied
            for city in flexible:
                if remaining_days[city] > 0:
                    return None
            # Also ensure day_pointer <= 25
            if day_pointer > 25:
                return None
            # Fill remaining days with last city if needed (but here all days are filled by fixed + placed)
            return schedule
        
        city = perm[index]
        needed = remaining_days[city]
        
        # Try to place this city starting at day_pointer
        # But must check connection from last city on previous day
        prev_city = None
        if day_pointer > 1:
            # Find which cities are on previous day
            prev_day_cities = schedule[day_pointer - 1]
            if prev_day_cities:
                prev_city = prev_day_cities[-1]  # last city visited previous day
        # If prev_city is None (day_pointer=1), it's start of trip
        
        # If prev_city exists and is not same as city, need direct flight
        if prev_city and prev_city != city:
            if not connected(prev_city, city):
                return None
        
        # Try to place needed days starting at day_pointer
        if day_pointer + needed - 1 > 25:
            return None
        
        # Check for overlap with fixed cities on these days
        for d in range(day_pointer, day_pointer + needed):
            if schedule[d] and schedule[d][-1] != city:
                # Overlap with another city's exclusive stay (except travel day double count)
                # Travel day double count allowed only if direct flight exists
                # For simplicity, we allow overlap only if it's a travel transition
                pass  # We'll handle by allowing one overlap per day (travel)
        
        # Place the city
        original_days = []
        for d in range(day_pointer, day_pointer + needed):
            original_days.append(schedule[d].copy())
            schedule[d].append(city)
        
        remaining_days[city] = 0
        
        # Move day_pointer: after placing, next city starts on last day of current city (overlap travel)
        new_day_pointer = day_pointer + needed
        
        # Recurse
        res = backtrack(index + 1, perm, new_day_pointer, remaining_days)
        if res is not None:
            return res
        
        # Backtrack
        for i, d in enumerate(range(day_pointer, day_pointer + needed)):
            schedule[d] = original_days[i]
        remaining_days[city] = needed
        
        return None
    
    # Try permutations of flexible cities
    from itertools import permutations
    for perm in permutations(flexible):
        # Reset remaining days for flexible cities
        remaining = {c: cities[c] for c in flexible}
        # Start after fixed cities? We start at day 1, but fixed cities already placed.
        # We need to find first empty day.
        first_empty = 1
        while first_empty <= 25 and schedule[first_empty]:
            first_empty += 1
        if first_empty > 25:
            first_empty = 25
        result = backtrack(0, perm, first_empty, remaining)
        if result is not None:
            # Convert schedule to itinerary format
            itinerary = []
            day = 1
            while day <= 25:
                cities_today = result[day]
                if not cities_today:
                    day += 1
                    continue
                # Find consecutive days with same set of cities
                start = day
                current_set = set(cities_today)
                while day <= 25 and set(result[day]) == current_set:
                    day += 1
                end = day - 1
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                # For display, if multiple cities in a day, show as travel day
                if len(current_set) == 1:
                    place = list(current_set)[0]
                else:
                    place = " → ".join(sorted(current_set))
                itinerary.append({"day_range": day_range, "place": place})
            return itinerary
    return None

itinerary = solve()
if itinerary:
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"error": "No feasible itinerary found"}, indent=2))