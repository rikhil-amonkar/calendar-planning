import json
from itertools import permutations

def solve():
    cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
    required_days = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2
    }
    
    direct_flights = [
        ("Milan", "Stockholm"),
        ("Munich", "Stockholm"),
        ("Bucharest", "Munich"),
        ("Munich", "Seville"),
        ("Stockholm", "Tallinn"),
        ("Munich", "Milan"),
        ("Munich", "Tallinn"),
        ("Seville", "Milan")
    ]
    
    # Make adjacency list
    adjacency = {city: set() for city in cities}
    for a, b in direct_flights:
        adjacency[a].add(b)
        adjacency[b].add(a)
    
    # Special constraints: (city, start_day, end_day) inclusive range must contain stay
    # We'll treat as: city must be visited within [start_day, end_day] for its entire required days
    # But here easier: we know exact placement from earlier reasoning
    # Let's do search over permutations of cities with day allocation
    
    total_days = 18
    
    # We'll search for sequence of (city, arrival_day, departure_day)
    # arrival_day <= departure_day, days in city = departure_day - arrival_day + 1
    # arrival_day of next = departure_day of previous (travel on same day)
    
    def dfs(current_city, day, visited_cities, schedule, remaining_days_req):
        if day > total_days:
            return False
        if len(visited_cities) == len(cities):
            # All cities visited, check if all required days met
            for city in cities:
                if remaining_days_req[city] != 0:
                    return False
            return True
        
        # Try next city
        for next_city in cities:
            if next_city in visited_cities:
                continue
            if next_city not in adjacency[current_city]:
                continue
            # Try to stay required days
            needed = remaining_days_req[next_city]
            if needed <= 0:
                continue
            # We can stay needed days starting at 'day'
            stay_end = day + needed - 1
            if stay_end > total_days:
                continue
            
            # Check special time constraints
            if next_city == "Bucharest":
                if not (1 <= day and stay_end <= 4):
                    continue
            if next_city == "Munich":
                if not (4 <= day and stay_end <= 8):
                    continue
            if next_city == "Seville":
                if not (8 <= day and stay_end <= 12):
                    continue
            
            # Update
            new_remaining = remaining_days_req.copy()
            new_remaining[next_city] = 0
            new_schedule = schedule + [(next_city, day, stay_end)]
            if dfs(next_city, stay_end, visited_cities | {next_city}, new_schedule, new_remaining):
                return new_schedule
        return False
    
    # Start from each possible first city
    for start_city in cities:
        if start_city != "Bucharest":
            continue  # Bucharest must be days 1-4, so likely start there
        needed_start = required_days[start_city]
        if needed_start != 4:
            continue
        stay_end = 1 + needed_start - 1
        if stay_end != 4:
            continue
        remaining = required_days.copy()
        remaining[start_city] = 0
        schedule = [(start_city, 1, stay_end)]
        result = dfs(start_city, stay_end, {start_city}, schedule, remaining)
        if result:
            # Convert to itinerary format
            itinerary = []
            for city, start, end in result:
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range, "place": city})
            
            # Output as JSON
            output = {"itinerary": itinerary}
            print(json.dumps(output, indent=2))
            return
    
    print('{"itinerary": []}')

if __name__ == "__main__":
    solve()