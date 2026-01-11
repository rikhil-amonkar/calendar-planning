import json
from itertools import combinations

# Cities and required days
cities = {
    "Paris": 5,
    "Warsaw": 2,
    "Krakow": 2,
    "Tallinn": 2,
    "Riga": 2,
    "Copenhagen": 5,
    "Helsinki": 5,
    "Oslo": 5,
    "Santorini": 2,
    "Lyon": 4
}

# Direct flights (undirected)
direct_flights = [
    ("Warsaw", "Riga"),
    ("Warsaw", "Tallinn"),
    ("Copenhagen", "Helsinki"),
    ("Lyon", "Paris"),
    ("Copenhagen", "Warsaw"),
    ("Lyon", "Oslo"),
    ("Paris", "Oslo"),
    ("Paris", "Riga"),
    ("Krakow", "Helsinki"),
    ("Paris", "Tallinn"),
    ("Oslo", "Riga"),
    ("Krakow", "Warsaw"),
    ("Paris", "Helsinki"),
    ("Copenhagen", "Santorini"),
    ("Helsinki", "Warsaw"),
    ("Helsinki", "Riga"),
    ("Copenhagen", "Krakow"),
    ("Copenhagen", "Riga"),
    ("Paris", "Krakow"),
    ("Copenhagen", "Oslo"),
    ("Oslo", "Tallinn"),
    ("Oslo", "Helsinki"),
    ("Copenhagen", "Tallinn"),
    ("Oslo", "Krakow"),
    ("Riga", "Tallinn"),
    ("Helsinki", "Tallinn"),
    ("Paris", "Copenhagen"),
    ("Paris", "Warsaw"),
    ("Santorini", "Oslo"),
    ("Oslo", "Warsaw")
]

# Make flight lookup set
flight_set = set()
for a, b in direct_flights:
    flight_set.add((a, b))
    flight_set.add((b, a))

# Fixed events: day -> city
fixed_events = {
    12: "Santorini",
    13: "Santorini",
    17: "Krakow",
    18: "Krakow",
    23: "Riga",
    24: "Riga",
    4: "Paris",
    5: "Paris",
    6: "Paris",
    7: "Paris",
    8: "Paris",
    # Helsinki friend days 18-22
    18: "Helsinki",  # conflict with Krakow, will handle by travel day
    19: "Helsinki",
    20: "Helsinki",
    21: "Helsinki",
    22: "Helsinki"
}

# Note: day 18 appears twice in fixed_events (Krakow and Helsinki) — we handle by allowing travel day.

# We'll search
def can_fly(city1, city2):
    return (city1, city2) in flight_set

def solve():
    days = 25
    # We'll store best schedule
    best_schedule = None
    
    # Backtracking search
    def backtrack(day, current_city, schedule, city_days_count, travel_days_used):
        nonlocal best_schedule
        
        if day > days:
            # Check if all cities' required days met
            if all(city_days_count[city] >= cities[city] for city in cities):
                # Valid schedule
                best_schedule = schedule[:]
            return
        
        # Prune: if remaining days + travel_days_used can't cover remaining required days
        remaining_days = days - day + 1
        remaining_city_days_needed = sum(max(0, cities[city] - city_days_count[city]) for city in cities)
        # Each remaining day can cover at most 1 new city-day if no travel, but with travel maybe 2
        # Max possible coverage = remaining_days + min(remaining_days - 1, ...) complex, skip for simplicity
        
        # Fixed event for this day
        fixed_city = fixed_events.get(day)
        
        # Option 1: Stay in current city
        if fixed_city is None or fixed_city == current_city:
            city_days_count[current_city] += 1
            schedule.append((day, current_city, current_city))  # start and end same
            backtrack(day + 1, current_city, schedule, city_days_count, travel_days_used)
            schedule.pop()
            city_days_count[current_city] -= 1
        
        # Option 2: Travel to another city (if direct flight exists)
        for next_city in cities:
            if next_city == current_city:
                continue
            if not can_fly(current_city, next_city):
                continue
            # Check fixed event: if fixed_city not None, we must be in fixed_city at end of day
            # So if fixed_city is not None, next_city must equal fixed_city
            if fixed_city is not None and next_city != fixed_city:
                continue
            # Also, if fixed_city is current_city, we can't leave it unless fixed_city is satisfied for the day?
            # Actually fixed event means we must be in that city on that day, so if fixed_city is current_city, we can't travel away.
            if fixed_city is not None and fixed_city == current_city:
                continue  # must stay
            
            # Travel day: count for both cities
            city_days_count[current_city] += 1
            city_days_count[next_city] += 1
            schedule.append((day, current_city, next_city))
            backtrack(day + 1, next_city, schedule, city_days_count, travel_days_used + 1)
            schedule.pop()
            city_days_count[next_city] -= 1
            city_days_count[current_city] -= 1
    
    # Try each starting city
    for start_city in cities:
        city_days_count = {city: 0 for city in cities}
        backtrack(1, start_city, [], city_days_count, 0)
        if best_schedule:
            break
    
    return best_schedule

# Run solver
schedule = solve()

if not schedule:
    print('{"itinerary": []}')
else:
    # Convert to itinerary format
    itinerary = []
    i = 0
    while i < len(schedule):
        day, start_city, end_city = schedule[i]
        if start_city == end_city:
            # Stay
            j = i
            while j < len(schedule) and schedule[j][1] == start_city and schedule[j][2] == start_city:
                j += 1
            itinerary.append({
                "day_range": f"Day {i+1}-{j}",
                "place": start_city
            })
            i = j
        else:
            # Travel day
            itinerary.append({
                "day_range": f"Day {i+1}",
                "place": f"{start_city} to {end_city}"
            })
            i += 1
    
    # Merge consecutive same places
    merged = []
    for item in itinerary:
        if merged and merged[-1]["place"] == item["place"]:
            # Extend range
            prev_range = merged[-1]["day_range"]
            # Simple merge for demo; in full solution parse ranges
            merged[-1]["day_range"] = f"Day {prev_range.split('-')[0].split()[1]}-{item['day_range'].split()[-1]}"
        else:
            merged.append(item)
    
    print(json.dumps({"itinerary": merged}))