import json
from itertools import permutations

def solve():
    cities = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
    required_days = {
        "Amsterdam": 4,
        "Edinburgh": 5,
        "Brussels": 5,
        "Vienna": 5,
        "Berlin": 4,
        "Reykjavik": 5
    }
    
    direct_flights = {
        ("Edinburgh", "Berlin"),
        ("Amsterdam", "Berlin"),
        ("Edinburgh", "Amsterdam"),
        ("Vienna", "Berlin"),
        ("Berlin", "Brussels"),
        ("Vienna", "Reykjavik"),
        ("Edinburgh", "Brussels"),
        ("Vienna", "Brussels"),
        ("Amsterdam", "Reykjavik"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Vienna"),
        ("Reykjavik", "Berlin")
    }
    
    # Make it undirected
    flight_set = set()
    for a, b in direct_flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    total_days = 23
    
    # We'll search over permutations of cities
    # and try to split days into consecutive stays
    
    def check_itinerary(seq, days_seq):
        # seq: list of city names in order
        # days_seq: list of days in each city
        # Check direct flights
        for i in range(len(seq) - 1):
            if (seq[i], seq[i + 1]) not in flight_set:
                return False
        
        # Check total days
        if sum(days_seq) != total_days:
            return False
        
        # Check required days per city
        city_days = {}
        for city, d in zip(seq, days_seq):
            city_days[city] = city_days.get(city, 0) + d
        for city in cities:
            if city_days.get(city, 0) != required_days[city]:
                return False
        
        # Check date constraints
        day = 1
        amsterdam_days = []
        reykjavik_days = []
        berlin_days = []
        for city, d in zip(seq, days_seq):
            for _ in range(d):
                if city == "Amsterdam":
                    amsterdam_days.append(day)
                if city == "Reykjavik":
                    reykjavik_days.append(day)
                if city == "Berlin":
                    berlin_days.append(day)
                day += 1
        
        # Amsterdam between day 5 and 8
        if not any(5 <= d <= 8 for d in amsterdam_days):
            return False
        # Reykjavik between day 12 and 16
        if not any(12 <= d <= 16 for d in reykjavik_days):
            return False
        # Berlin between day 16 and 19
        if not any(16 <= d <= 19 for d in berlin_days):
            return False
        
        return True
    
    # Generate all permutations of cities
    for perm in permutations(cities):
        # We need to split 23 days into 6 positive integers matching required_days
        # But order is fixed by perm, so we just assign days_seq = required_days in that order
        # Wait, a city can appear multiple times in sequence, so we need to consider partitions.
        # Let's simplify: each city appears exactly once in sequence (because we can merge consecutive same city).
        # So we just assign days_seq[i] = required_days[perm[i]]
        days_seq = [required_days[city] for city in perm]
        
        if check_itinerary(perm, days_seq):
            # Build itinerary
            itinerary = []
            day_start = 1
            for city, days in zip(perm, days_seq):
                day_end = day_start + days - 1
                itinerary.append({
                    "day_range": f"Day {day_start}-{day_end}",
                    "place": city
                })
                day_start = day_end + 1
            return itinerary
    
    return None

def main():
    itinerary = solve()
    if itinerary is None:
        print('{"error": "No valid itinerary found"}')
    else:
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()