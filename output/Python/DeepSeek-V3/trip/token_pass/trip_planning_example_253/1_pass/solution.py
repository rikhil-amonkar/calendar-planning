import json
from itertools import permutations

def solve():
    cities = ["Vienna", "Lyon", "Amsterdam", "Santorini"]
    direct_flights = {
        ("Vienna", "Lyon"), ("Lyon", "Vienna"),
        ("Vienna", "Santorini"), ("Santorini", "Vienna"),
        ("Vienna", "Amsterdam"), ("Amsterdam", "Vienna"),
        ("Amsterdam", "Santorini"), ("Santorini", "Amsterdam"),
        ("Lyon", "Amsterdam"), ("Amsterdam", "Lyon")
    }
    
    required_days = {
        "Vienna": 7,
        "Lyon": 3,
        "Amsterdam": 3,
        "Santorini": 4
    }
    
    total_days = 14
    
    # Event constraints: (city, start_day, end_day inclusive)
    events = [
        ("Lyon", 7, 9),
        ("Amsterdam", 9, 11)
    ]
    
    # Try all permutations of city visit order
    for perm in permutations(cities):
        # Check direct flights between consecutive cities
        valid_order = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i + 1]) not in direct_flights:
                valid_order = False
                break
        if not valid_order:
            continue
        
        # We have 4 cities, 3 travel days
        # Let's brute-force over possible travel days (between 1 and 13)
        # Travel days: t1 between city1 and city2, t2 between city2 and city3, t3 between city3 and city4
        # t1 < t2 < t3, all integers 1..13
        for t1 in range(1, total_days):
            for t2 in range(t1 + 1, total_days):
                for t3 in range(t2 + 1, total_days):
                    # Day blocks:
                    # City1: day 1 to t1 (inclusive)
                    # City2: day t1 to t2 (inclusive)
                    # City3: day t2 to t3 (inclusive)
                    # City4: day t3 to total_days (inclusive)
                    stays = {
                        perm[0]: (1, t1),
                        perm[1]: (t1, t2),
                        perm[2]: (t2, t3),
                        perm[3]: (t3, total_days)
                    }
                    
                    # Check required days per city
                    days_count = {city: 0 for city in cities}
                    for city, (start, end) in stays.items():
                        days_count[city] += (end - start + 1)
                    
                    if all(days_count[city] == required_days[city] for city in cities):
                        # Check event constraints
                        event_ok = True
                        for city, estart, eend in events:
                            s, e = stays[city]
                            if not (s <= estart and eend <= e):
                                event_ok = False
                                break
                        if event_ok:
                            # Build itinerary
                            itinerary = []
                            for city, (start, end) in stays.items():
                                if start == end:
                                    day_range = f"Day {start}"
                                else:
                                    day_range = f"Day {start}-{end}"
                                itinerary.append({"day_range": day_range, "place": city})
                            return itinerary
    return None

def main():
    itinerary = solve()
    if itinerary is None:
        print(json.dumps({"error": "No valid itinerary found"}))
    else:
        print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()