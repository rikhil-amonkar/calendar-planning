import json
from itertools import product

def is_connected(city1, city2):
    flights = {
        ("Vienna", "Stockholm"),
        ("Vienna", "Nice"),
        ("Vienna", "Split"),
        ("Stockholm", "Split"),
        ("Nice", "Stockholm"),
        ("Stockholm", "Vienna"),
        ("Nice", "Vienna"),
        ("Split", "Vienna"),
        ("Split", "Stockholm"),
        ("Stockholm", "Nice")
    }
    return (city1, city2) in flights or city1 == city2

def count_days(itinerary):
    # itinerary is list of (city1, city2) for each day, city2 may be None
    counts = {"Vienna": 0, "Stockholm": 0, "Nice": 0, "Split": 0}
    for city1, city2 in itinerary:
        counts[city1] += 1
        if city2:
            counts[city2] += 1
    return counts

def check_constraints(itinerary):
    # Day 7 and Day 9 in Split
    if itinerary[6][0] != "Split" and (itinerary[6][1] != "Split" if itinerary[6][1] else True):
        return False
    if itinerary[8][0] != "Split" and (itinerary[8][1] != "Split" if itinerary[8][1] else True):
        return False
    
    # Day 1 or Day 2 in Vienna
    day1_cities = [itinerary[0][0]]
    if itinerary[0][1]:
        day1_cities.append(itinerary[0][1])
    day2_cities = [itinerary[1][0]]
    if itinerary[1][1]:
        day2_cities.append(itinerary[1][1])
    if "Vienna" not in day1_cities and "Vienna" not in day2_cities:
        return False
    
    # Travel connectivity
    prev_city = None
    for city1, city2 in itinerary:
        if prev_city and not is_connected(prev_city, city1):
            return False
        if city2:
            if not is_connected(city1, city2):
                return False
            prev_city = city2
        else:
            prev_city = city1
    
    # Count days
    counts = count_days(itinerary)
    required = {"Vienna": 2, "Stockholm": 5, "Nice": 2, "Split": 3}
    return counts == required

def generate_itinerary():
    cities = ["Vienna", "Stockholm", "Nice", "Split"]
    # We'll brute force over possible sequences
    # Each day: (city1, city2) where city2 may be None or another city
    # Simplify: only allow travel on at most 3 days (since we need 3 double-count days)
    
    # We can brute force by considering each day as either 1 city or 2 cities
    # but to reduce search, note: Split fixed on day 7 and 9, Vienna on day 1 or 2.
    
    # Let's manually deduce and encode the solution we found logically:
    
    # After trial and error, one valid itinerary:
    # Day 1: Vienna
    # Day 2: Vienna → Stockholm (Vienna day 2, Stockholm day 2)
    # Day 3: Stockholm
    # Day 4: Stockholm
    # Day 5: Stockholm
    # Day 6: Stockholm → Split (Stockholm day 6, Split day 6)
    # Day 7: Split
    # Day 8: Split → Nice (Split day 8, Nice day 8)
    # Day 9: Split
    
    # But this gives Split 4 days. We need Split 3 days.
    # So remove Split from one day. Can't remove 7 or 9. Remove day 8 Split? Then day 8 is only Nice, but then Split total = 2 (day 6,7,9? Wait day 9 is Split, day 7 Split, day 6 Split → 3). Yes!
    # So:
    # Day 8: Nice (travel from Split to Nice on day 8 morning, so Split not counted on day 8)
    # But then Nice only day 8 → 1 day, need 2. So need another Nice day.
    # Add Nice on day 1? Then Vienna loses a day.
    # Let's try:
    # Day 1: Vienna → Nice (Vienna day1, Nice day1)
    # Day 2: Nice → Stockholm (Nice day2, Stockholm day2)
    # Day 3: Stockholm
    # Day 4: Stockholm
    # Day 5: Stockholm
    # Day 6: Stockholm → Split (Stockholm day6, Split day6)
    # Day 7: Split
    # Day 8: Split → Nice (Split day8, Nice day8)
    # Day 9: Split
    # Counts:
    # Vienna: day1 → 1 ❌ need 2 → fails.
    
    # Let's search programmatically:
    
    # We'll do a DFS for 9 days
    def dfs(day, current_city, counts, itinerary_days, travel_days_used):
        if day == 9:
            # Check if counts match required
            required = {"Vienna": 2, "Stockholm": 5, "Nice": 2, "Split": 3}
            if counts != required:
                return None
            # Check day 7 and 9 in Split
            if not (itinerary_days[6][0] == "Split" or (itinerary_days[6][1] == "Split" if itinerary_days[6][1] else False)):
                return None
            if not (itinerary_days[8][0] == "Split" or (itinerary_days[8][1] == "Split" if itinerary_days[8][1] else False)):
                return None
            # Check day 1 or 2 in Vienna
            day1_ok = itinerary_days[0][0] == "Vienna" or (itinerary_days[0][1] == "Vienna" if itinerary_days[0][1] else False)
            day2_ok = itinerary_days[1][0] == "Vienna" or (itinerary_days[1][1] == "Vienna" if itinerary_days[1][1] else False)
            if not (day1_ok or day2_ok):
                return None
            return itinerary_days
        
        # Try staying in current city
        new_counts = counts.copy()
        new_counts[current_city] += 1
        new_itinerary = itinerary_days + [(current_city, None)]
        res = dfs(day+1, current_city, new_counts, new_itinerary, travel_days_used)
        if res:
            return res
        
        # Try traveling to another city if travel_days_used < 3
        if travel_days_used < 3:
            for next_city in cities:
                if next_city != current_city and is_connected(current_city, next_city):
                    new_counts2 = counts.copy()
                    new_counts2[current_city] += 1
                    new_counts2[next_city] += 1
                    new_itinerary2 = itinerary_days + [(current_city, next_city)]
                    res = dfs(day+1, next_city, new_counts2, new_itinerary2, travel_days_used+1)
                    if res:
                        return res
        return None
    
    # Start DFS from each possible city on day 1
    for start_city in cities:
        counts = {c: 0 for c in cities}
        counts[start_city] = 1
        itinerary = [(start_city, None)]
        result = dfs(1, start_city, counts, itinerary, 0)
        if result:
            return result
    
    return None

def format_output(itinerary):
    # itinerary is list of (city1, city2)
    # Convert to day ranges
    day_place_ranges = []
    i = 0
    while i < len(itinerary):
        start_day = i + 1
        city1, city2 = itinerary[i]
        if city2 is None:
            # Single city day
            day_place_ranges.append({"day_range": f"Day {start_day}", "place": city1})
            i += 1
        else:
            # Travel day
            day_place_ranges.append({"day_range": f"Day {start_day}", "place": f"{city1} → {city2}"})
            i += 1
    return {"itinerary": day_place_ranges}

def main():
    itinerary = generate_itinerary()
    if itinerary:
        output = format_output(itinerary)
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()