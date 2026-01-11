import json
from itertools import permutations

def solve():
    # Cities and required days
    cities = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2
    }
    
    # Direct flights (undirected)
    flights = {
        "Hamburg": {"Frankfurt", "Porto", "Geneva", "Manchester"},
        "Frankfurt": {"Hamburg", "Geneva", "Porto", "Naples", "Manchester"},
        "Naples": {"Mykonos", "Manchester", "Frankfurt", "Geneva"},
        "Mykonos": {"Naples", "Geneva"},
        "Geneva": {"Hamburg", "Mykonos", "Frankfurt", "Porto", "Manchester", "Naples"},
        "Porto": {"Hamburg", "Frankfurt", "Geneva", "Manchester"},
        "Manchester": {"Geneva", "Naples", "Frankfurt", "Porto", "Hamburg"}
    }
    
    # Special constraints
    # Manchester wedding days 15-18 inclusive
    manchester_wedding_days = set(range(15, 19))  # days 15,16,17,18
    # Mykonos friend days 10-12 inclusive
    mykonos_friend_days = set(range(10, 13))
    # Frankfurt show day 5 or 6
    frankfurt_show_days = {5, 6}
    
    total_days = 18
    
    # We'll search over permutations of cities to visit order
    city_names = list(cities.keys())
    
    # Helper to check if two cities are connected
    def connected(c1, c2):
        return c2 in flights[c1]
    
    # Backtracking search
    def backtrack(assignment, remaining_cities, current_day):
        if current_day > total_days:
            return None
        if not remaining_cities:
            # All cities assigned, check total days
            total_assigned = sum(end - start for (_, start, end) in assignment)
            if total_assigned == total_days:
                return assignment
            return None
        
        for city in remaining_cities:
            dur = cities[city]
            start_day = current_day
            end_day = start_day + dur
            if end_day > total_days + 1:
                continue
            
            # Check connectivity with previous city
            if assignment:
                prev_city = assignment[-1][0]
                if not connected(prev_city, city):
                    continue
            
            # Special constraints for specific cities
            if city == "Manchester":
                # Must cover days 15-18
                manchester_days = set(range(start_day, end_day))
                if not manchester_wedding_days.issubset(manchester_days):
                    continue
            if city == "Mykonos":
                mykonos_days = set(range(start_day, end_day))
                if not (mykonos_days & mykonos_friend_days):
                    continue
            if city == "Frankfurt":
                frankfurt_days = set(range(start_day, end_day))
                if not (frankfurt_days & frankfurt_show_days):
                    continue
            
            new_assignment = assignment + [(city, start_day, end_day)]
            new_remaining = [c for c in remaining_cities if c != city]
            res = backtrack(new_assignment, new_remaining, end_day)
            if res is not None:
                return res
        return None
    
    # Try different permutations because order matters for connectivity
    for perm in permutations(city_names):
        result = backtrack([], list(perm), 1)
        if result:
            # Format result
            itinerary = []
            for city, start, end in result:
                if end - start == 1:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end-1}"
                itinerary.append({"day_range": day_range, "place": city})
            return {"itinerary": itinerary}
    
    return {"itinerary": []}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))