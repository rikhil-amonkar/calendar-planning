import json

def main():
    # Cities and required days
    cities = {
        "Frankfurt": 4,
        "Manchester": 4,
        "Valencia": 4,
        "Naples": 4,
        "Oslo": 3,
        "Vilnius": 2
    }
    
    # Fixed constraints
    total_days = 16
    frankfurt_last_days = list(range(13, 17))  # days 13-16 in Frankfurt
    wedding_day = 12  # wedding in Vilnius between day 12 and 13
    
    # Direct flights graph
    direct_flights = {
        "Valencia": ["Frankfurt", "Naples"],
        "Manchester": ["Frankfurt", "Naples", "Oslo"],
        "Naples": ["Manchester", "Frankfurt", "Oslo", "Valencia"],
        "Oslo": ["Frankfurt", "Naples", "Vilnius", "Manchester"],
        "Vilnius": ["Frankfurt", "Oslo"],
        "Frankfurt": ["Valencia", "Manchester", "Naples", "Oslo", "Vilnius"]
    }
    
    # We'll construct the itinerary based on the derived schedule
    itinerary = []
    
    # Day 1-4: Valencia
    itinerary.append({"day_range": "Day 1-4", "place": "Valencia"})
    # Day 4: travel to Naples (counts for both Valencia and Naples)
    # Day 4-7: Naples
    itinerary.append({"day_range": "Day 4-7", "place": "Naples"})
    # Day 7: travel to Manchester
    # Day 7-10: Manchester
    itinerary.append({"day_range": "Day 7-10", "place": "Manchester"})
    # Day 10: travel to Oslo
    # Day 10-12: Oslo
    itinerary.append({"day_range": "Day 10-12", "place": "Oslo"})
    # Day 12: travel to Vilnius
    # Day 12-13: Vilnius
    itinerary.append({"day_range": "Day 12-13", "place": "Vilnius"})
    # Day 13: travel to Frankfurt
    # Day 13-16: Frankfurt
    itinerary.append({"day_range": "Day 13-16", "place": "Frankfurt"})
    
    # Verify counts
    day_counts = {city: 0 for city in cities}
    for entry in itinerary:
        place = entry["place"]
        day_range = entry["day_range"]
        # Parse day range
        if "-" in day_range:
            start, end = day_range.replace("Day ", "").split("-")
            start_day = int(start)
            end_day = int(end)
            days = end_day - start_day + 1
        else:
            # Single day
            day = int(day_range.replace("Day ", ""))
            days = 1
        day_counts[place] += days
    
    # Check against requirements
    for city, req in cities.items():
        if day_counts[city] != req:
            print(f"Error: {city} has {day_counts[city]} days, required {req}")
            return
    
    # Check Frankfurt last days
    frankfurt_days = []
    for entry in itinerary:
        if entry["place"] == "Frankfurt":
            day_range = entry["day_range"]
            start, end = day_range.replace("Day ", "").split("-")
            frankfurt_days.extend(range(int(start), int(end) + 1))
    if not all(day in frankfurt_days for day in frankfurt_last_days):
        print("Error: Frankfurt does not cover days 13-16")
        return
    
    # Check wedding in Vilnius between day 12 and 13
    vilnius_days = []
    for entry in itinerary:
        if entry["place"] == "Vilnius":
            day_range = entry["day_range"]
            start, end = day_range.replace("Day ", "").split("-")
            vilnius_days.extend(range(int(start), int(end) + 1))
    if 12 not in vilnius_days:
        print("Error: Wedding day 12 not in Vilnius")
        return
    
    # Check direct flights connectivity
    route = [entry["place"] for entry in itinerary]
    # Simplify to unique consecutive cities
    unique_route = []
    for city in route:
        if not unique_route or city != unique_route[-1]:
            unique_route.append(city)
    
    for i in range(len(unique_route) - 1):
        from_city = unique_route[i]
        to_city = unique_route[i + 1]
        if to_city not in direct_flights.get(from_city, []):
            print(f"Error: No direct flight from {from_city} to {to_city}")
            return
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()