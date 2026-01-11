import json
from itertools import permutations

def total_days_in_itinerary(itinerary):
    # itinerary is list of (city, start_day, end_day inclusive)
    days_count = {city: 0 for city in ["Naples", "Seville", "Milan"]}
    for city, start, end in itinerary:
        for day in range(start, end + 1):
            days_count[city] += 1
    return days_count

def is_valid_itinerary(itinerary):
    # Check total days = 12
    last_day = max(end for _, _, end in itinerary)
    if last_day != 12:
        return False
    
    # Check Seville days 9-12 inclusive
    seville_days = []
    for city, start, end in itinerary:
        if city == "Seville":
            for day in range(start, end + 1):
                seville_days.append(day)
    if set(seville_days) != set([9, 10, 11, 12]):
        return False
    
    # Check direct flights
    cities_order = [itinerary[i][0] for i in range(len(itinerary))]
    for i in range(len(cities_order) - 1):
        a, b = cities_order[i], cities_order[i + 1]
        if not ((a == "Milan" and b == "Seville") or
                (a == "Seville" and b == "Milan") or
                (a == "Naples" and b == "Milan") or
                (a == "Milan" and b == "Naples")):
            return False
    
    # Count days per city
    counts = total_days_in_itinerary(itinerary)
    if counts["Naples"] != 3:
        return False
    if counts["Seville"] != 4:
        return False
    if counts["Milan"] != 7:
        return False
    
    return True

def generate_itineraries():
    cities = ["Naples", "Seville", "Milan"]
    valid = []
    
    # We know Seville must be days 9-12, so only two possible slots for Naples and Milan before/after
    # Possible orders: Naples, Milan, Seville  or  Milan, Naples, Seville? But Naples-Seville not directly connected, so must have Milan between them.
    # So possible city sequences:
    # 1. Naples -> Milan -> Seville
    # 2. Milan -> Naples -> Milan -> Seville  (but Milan repeated, possible? Yes, but then Milan split into two stays)
    # We'll brute force start days for each segment.
    
    # Try order: Naples, Milan, Seville
    for naples_start in range(1, 9):
        for naples_end in range(naples_start, 9):
            naples_len = naples_end - naples_start + 1
            if naples_len > 3:
                continue
            for milan_start in range(naples_end, 9):
                milan_end = 8
                for milan_end in range(milan_start, 9):
                    milan_len = milan_end - milan_start + 1
                    # Seville fixed 9-12
                    seville_start = 9
                    seville_end = 12
                    # Check transition days count
                    itinerary = [
                        ("Naples", naples_start, naples_end),
                        ("Milan", milan_start, milan_end),
                        ("Seville", seville_start, seville_end)
                    ]
                    # Adjust for travel overlap: if cities adjacent in itinerary, end day of previous = start day of next
                    # We'll enforce that
                    if naples_end != milan_start - 1:
                        # They must be consecutive days with overlap? Actually rule: if fly on day X, both cities count day X.
                        # So milan_start should equal naples_end (same day travel)
                        continue
                    if milan_end != seville_start - 1:
                        # milan_end should equal seville_start for same day travel
                        continue
                    # Now adjust: travel days count for both, so extend each segment to include start day of next?
                    # Actually in our counting, naples_end is last day in Naples, also first day in Milan if milan_start = naples_end.
                    # So milan_start = naples_end, and seville_start = milan_end.
                    # Then recompute counts:
                    itinerary = [
                        ("Naples", naples_start, naples_end),
                        ("Milan", naples_end, milan_end),
                        ("Seville", milan_end, seville_end)
                    ]
                    if is_valid_itinerary(itinerary):
                        valid.append(itinerary)
    
    return valid

def main():
    valid_itineraries = generate_itineraries()
    if not valid_itineraries:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Take first valid itinerary
    itinerary = valid_itineraries[0]
    
    # Convert to required JSON format
    result = {"itinerary": []}
    for city, start, end in itinerary:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        result["itinerary"].append({"day_range": day_range, "place": city})
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()