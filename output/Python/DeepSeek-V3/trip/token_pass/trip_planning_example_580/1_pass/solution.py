import json
from itertools import permutations

def solve():
    cities = ['Geneva', 'Paris', 'Porto', 'Reykjavik', 'Oslo']
    required_days = {
        'Geneva': 7,
        'Paris': 6,
        'Porto': 7,
        'Reykjavik': 2,
        'Oslo': 5
    }
    
    direct_flights = {
        ('Paris', 'Oslo'),
        ('Geneva', 'Oslo'),
        ('Porto', 'Paris'),
        ('Geneva', 'Paris'),
        ('Geneva', 'Porto'),
        ('Paris', 'Reykjavik'),
        ('Reykjavik', 'Oslo'),
        ('Porto', 'Oslo'),
        # make symmetric
    }
    # make symmetric
    direct_flights_sym = set()
    for a, b in direct_flights:
        direct_flights_sym.add((a, b))
        direct_flights_sym.add((b, a))
    direct_flights = direct_flights_sym
    
    total_calendar_days = 23
    
    # Fixed constraints
    # Geneva days 1-7
    # Oslo days 19-23
    
    # We'll represent schedule as list of (city, start_day, end_day)
    # where end_day is inclusive, and travel days are overlaps.
    
    # We can brute-force order of cities between fixed blocks.
    # Geneva (1-7), then some sequence of other cities, ending with Oslo (19-23).
    # Remaining cities: Paris, Porto, Reykjavik.
    # They must be visited between day 8 and day 18, with overlaps.
    
    # Let's enumerate permutations of [Paris, Porto, Reykjavik]
    possible_orders = list(permutations(['Paris', 'Porto', 'Reykjavik']))
    
    def days_for_city_in_schedule(schedule):
        # schedule: list of (city, start, end) inclusive, with overlaps possible at boundaries
        days_count = {city: 0 for city in cities}
        for i, (city, start, end) in enumerate(schedule):
            for day in range(start, end + 1):
                days_count[city] += 1
        return days_count
    
    def overlaps_ok(schedule):
        # Check no day has >2 cities (impossible in reality but here max is travel day = 2 cities)
        # Actually, we just ensure total city-days = required_days sum
        days_count = days_for_city_in_schedule(schedule)
        total_city_days = sum(days_count.values())
        # Total city-days should be sum(required) = 27
        if total_city_days != 27:
            return False
        # Each city's days must match required
        for city in cities:
            if days_count[city] != required_days[city]:
                return False
        # Check direct flights between consecutive cities in schedule
        for i in range(len(schedule) - 1):
            city1 = schedule[i][0]
            city2 = schedule[i + 1][0]
            if (city1, city2) not in direct_flights:
                return False
        return True
    
    solutions = []
    
    for order in possible_orders:
        # We have Geneva fixed: day 1-7
        # Then order[0] starts day 8 (overlap with Geneva? yes, travel day 8)
        # Then order[1] starts after order[0] ends (with overlap)
        # Then order[2] starts after order[1] ends (with overlap)
        # Then Oslo starts day 19 (overlap with last of order[2])
        
        # Let's brute-force possible end days for each segment
        # day indices: Geneva: 1-7
        # Let a = end day of order[0] (inclusive)
        # Let b = end day of order[1]
        # Let c = end day of order[2]
        # Constraints: 8 <= a <= 18, a < b <= 18, b < c <= 18, c >= 19? No, c <= 18, Oslo starts 19.
        # Actually c ends day 18 at latest, Oslo starts 19.
        
        for a_end in range(8, 19):
            for b_end in range(a_end + 1, 19):
                for c_end in range(b_end + 1, 19):
                    # Build schedule
                    schedule = [
                        ('Geneva', 1, 7),
                        (order[0], 8, a_end),
                        (order[1], a_end, b_end),  # travel day a_end counts for both
                        (order[2], b_end, c_end),
                        ('Oslo', c_end, 23)  # travel day c_end counts for both
                    ]
                    # Check days counts
                    if overlaps_ok(schedule):
                        solutions.append(schedule)
    
    # Take first solution
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    schedule = solutions[0]
    
    # Convert to itinerary format
    itinerary = []
    for city, start, end in schedule:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))