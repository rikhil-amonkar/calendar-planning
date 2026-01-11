import itertools
import json

def solve():
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    required_days = {
        "Dublin": 5,
        "Helsinki": 3,
        "Riga": 3,
        "Reykjavik": 2,
        "Vienna": 2,
        "Tallinn": 5
    }
    
    direct_flights = {
        ("Helsinki", "Riga"),
        ("Riga", "Tallinn"),
        ("Vienna", "Helsinki"),
        ("Riga", "Dublin"),
        ("Vienna", "Riga"),
        ("Reykjavik", "Vienna"),
        ("Helsinki", "Dublin"),
        ("Tallinn", "Dublin"),
        ("Reykjavik", "Helsinki"),
        ("Reykjavik", "Dublin"),
        ("Helsinki", "Tallinn"),
        ("Vienna", "Dublin")
    }
    # Make it undirected
    flights = set()
    for a, b in direct_flights:
        flights.add((a, b))
        flights.add((b, a))
    
    # Special constraints: day ranges are 1-based inclusive
    # Helsinki between day 3 and 5 means at least one of days 3,4,5 in Helsinki
    # But better: Helsinki days must include days 3,4,5 fully? Let's interpret as "Helsinki days must cover day 3 to day 5 inclusive"
    # Vienna must include days 2 and 3
    # Tallinn must include days 7 to 11 inclusive
    
    def check_constraints(schedule):
        # schedule: list of (city, start_day, end_day) with end_day inclusive
        # Check total days = 15
        if schedule[-1][2] != 15:
            return False
        
        # Check each city's total days
        days_per_city = {city: 0 for city in cities}
        for city, start, end in schedule:
            days_per_city[city] += (end - start + 1)
        
        for city in cities:
            if days_per_city[city] != required_days[city]:
                return False
        
        # Check direct flights
        for i in range(len(schedule) - 1):
            if (schedule[i][0], schedule[i+1][0]) not in flights:
                return False
        
        # Check special day constraints
        # Build day -> city mapping (a day can be in two cities if travel)
        day_cities = {day: [] for day in range(1, 16)}
        for city, start, end in schedule:
            for day in range(start, end + 1):
                day_cities[day].append(city)
        
        # Vienna days 2-3
        if not ("Vienna" in day_cities[2] and "Vienna" in day_cities[3]):
            return False
        
        # Helsinki days 3-5
        hel_ok = False
        for day in [3, 4, 5]:
            if "Helsinki" in day_cities[day]:
                hel_ok = True
                break
        if not hel_ok:
            return False
        
        # Tallinn days 7-11
        for day in range(7, 12):
            if "Tallinn" not in day_cities[day]:
                return False
        
        return True
    
    # Generate permutations of cities
    for perm in itertools.permutations(cities):
        # We need to split 15 days into 6 blocks with block lengths >= required_days[city]
        # But because of travel days counting for both, block length can be equal to required days
        # We'll try all possible start days for each city in sequence
        # This is a DFS for start days
        def dfs(idx, current_schedule, last_end_day):
            if idx == len(perm):
                if last_end_day == 15 and check_constraints(current_schedule):
                    return current_schedule
                return None
            
            city = perm[idx]
            req = required_days[city]
            # start_day must be >= last_end_day (if same, it's a travel day overlapping)
            # end_day = start_day + req - 1
            # end_day <= 15
            for start in range(last_end_day, 16):
                end = start + req - 1
                if end > 15:
                    break
                new_schedule = current_schedule + [(city, start, end)]
                res = dfs(idx + 1, new_schedule, end)
                if res is not None:
                    return res
            return None
        
        result_schedule = dfs(0, [], 1)
        if result_schedule is not None:
            # Convert to required JSON format
            itinerary = []
            for city, start, end in result_schedule:
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range, "place": city})
            
            return {"itinerary": itinerary}
    
    return {"itinerary": []}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))