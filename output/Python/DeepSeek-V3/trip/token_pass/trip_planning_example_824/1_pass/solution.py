import json
from typing import List, Dict, Tuple, Optional

# Cities
CITIES = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]

# Required days per city
REQUIRED_DAYS = {
    "Berlin": 5,
    "Split": 3,
    "Bucharest": 3,
    "Riga": 5,
    "Lisbon": 3,
    "Tallinn": 4,
    "Lyon": 5
}

# Direct flights (undirected)
FLIGHTS = [
    ("Lisbon", "Bucharest"),
    ("Berlin", "Lisbon"),
    ("Bucharest", "Riga"),
    ("Berlin", "Riga"),
    ("Split", "Lyon"),
    ("Lisbon", "Riga"),
    ("Riga", "Tallinn"),
    ("Berlin", "Split"),
    ("Lyon", "Lisbon"),
    ("Berlin", "Tallinn"),
    ("Lyon", "Bucharest")
]

# Make adjacency list
ADJ = {city: set() for city in CITIES}
for a, b in FLIGHTS:
    ADJ[a].add(b)
    ADJ[b].add(a)

# Fixed constraints: day -> city (if any)
FIXED = {}
for day in range(1, 6):
    FIXED[day] = "Berlin"
for day in range(7, 12):
    FIXED[day] = "Lyon"
for day in range(13, 16):
    FIXED[day] = "Bucharest"

TOTAL_DAYS = 22

def dfs(day: int, current_city: str, days_in_city: Dict[str, int], itinerary: List[Tuple[int, int, str]]) -> Optional[List[Tuple[int, int, str]]]:
    """
    day: current day (1-based), we are in current_city from start of this day
    days_in_city: total days spent in each city so far (counting travel days as in both cities)
    itinerary: list of (start_day, end_day, city) for stays so far (end_day is last day in city without travel)
    """
    if day > TOTAL_DAYS:
        # Check if all cities have required days
        for city, req in REQUIRED_DAYS.items():
            if days_in_city.get(city, 0) != req:
                return None
        return itinerary
    
    # If this day is fixed to a city, we must be in that city
    if day in FIXED:
        if FIXED[day] != current_city:
            return None
    
    # Try staying in current city for k more days (including today)
    max_stay = TOTAL_DAYS - day + 1
    for stay_length in range(1, max_stay + 1):
        end_day = day + stay_length - 1
        # Check fixed constraints during this stay
        valid = True
        for d in range(day, end_day + 1):
            if d in FIXED and FIXED[d] != current_city:
                valid = False
                break
        if not valid:
            continue
        
        # Update days_in_city for this stay
        new_days_in_city = days_in_city.copy()
        for d in range(day, end_day + 1):
            new_days_in_city[current_city] = new_days_in_city.get(current_city, 0) + 1
        
        # If this is the last stay, check final requirement
        if end_day == TOTAL_DAYS:
            # All days done, check requirements
            if all(new_days_in_city.get(c, 0) == REQUIRED_DAYS[c] for c in CITIES):
                return itinerary + [(day, end_day, current_city)]
            continue
        
        # Otherwise, need to travel on next day (end_day + 1)
        travel_day = end_day + 1
        if travel_day > TOTAL_DAYS:
            continue
        
        # Travel day must satisfy fixed constraint
        if travel_day in FIXED:
            next_city = FIXED[travel_day]
            if next_city not in ADJ[current_city]:
                continue
        else:
            # Try all possible next cities connected by direct flight
            next_candidates = [nc for nc in ADJ[current_city]]
            # Filter by not exceeding required days
            next_candidates = [nc for nc in next_candidates if new_days_in_city.get(nc, 0) < REQUIRED_DAYS[nc]]
        
        # For each possible next city
        for next_city in (next_candidates if 'next_candidates' in locals() else [FIXED[travel_day]] if travel_day in FIXED else []):
            # On travel day, you are in both cities
            updated_days = new_days_in_city.copy()
            updated_days[current_city] = updated_days.get(current_city, 0) + 1
            updated_days[next_city] = updated_days.get(next_city, 0) + 1
            
            # Recurse
            new_itinerary = itinerary + [(day, end_day, current_city)]
            res = dfs(travel_day, next_city, updated_days, new_itinerary)
            if res is not None:
                return res
    
    return None

def solve() -> Dict:
    # Start on day 1 in Berlin (fixed)
    start_city = "Berlin"
    days_in_city = {start_city: 0}
    itinerary = []
    
    result = dfs(1, start_city, days_in_city, itinerary)
    
    if result is None:
        return {"itinerary": []}
    
    # Convert to required output format
    output = []
    for start, end, city in result:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        output.append({"day_range": day_range, "place": city})
    
    return {"itinerary": output}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))