import json

def main():
    total_days = 15

    # Define required stays (days required in each city, not counting overlap flights)
    # Note: When flying on a day, that day is counted for both origin and destination.
    requirements = {
        "Vienna": 4,   # Including conference day on day1 and day4.
        "Rome": 3,
        "Riga": 2,
        "Vilnius": 4,
        "Milan": 2,
        "Lisbon": 3,
        "Oslo": 3
    }
    
    # Define special day constraints:
    # Vienna: Conference on day1 and day4.
    # Lisbon: Visit relatives between day11 and day13 (at least one Lisbon day in that interval needed).
    # Oslo: Meet friend between day13 and day15 (at least one Oslo day in that interval needed).
    special = {
        "Vienna": [1, 4],
        "Lisbon": list(range(11, 14)),  # one of Lisbon days must be within [11,13]
        "Oslo": list(range(13, 16))     # one of Oslo days must be within [13,15]
    }
    
    # Direct flights available (treating most as bidirectional except those specified as "from")
    # We represent flights as a dictionary with tuple keys. For directional ones, we mark accordingly.
    flights = {
        ("Riga", "Oslo"): True,
        ("Oslo", "Riga"): True,
        ("Rome", "Oslo"): True,
        ("Oslo", "Rome"): True,
        ("Vienna", "Milan"): True,
        ("Milan", "Vienna"): True,
        ("Vienna", "Vilnius"): True,
        ("Vilnius", "Vienna"): True,
        ("Vienna", "Lisbon"): True,
        ("Lisbon", "Vienna"): True,
        ("Riga", "Milan"): True,
        ("Milan", "Riga"): True,
        ("Lisbon", "Oslo"): True,
        ("Oslo", "Lisbon"): True,
        ("Rome", "Riga"): True,     # directional: from Rome to Riga
        ("Riga", "Rome"): False,
        ("Rome", "Lisbon"): True,
        ("Lisbon", "Rome"): True,
        ("Vienna", "Riga"): True,
        ("Riga", "Vienna"): True,
        ("Vienna", "Rome"): True,
        ("Rome", "Vienna"): True,
        ("Milan", "Oslo"): True,
        ("Oslo", "Milan"): True,
        ("Vienna", "Oslo"): True,
        ("Oslo", "Vienna"): True,
        ("Vilnius", "Oslo"): True,
        ("Oslo", "Vilnius"): True,
        ("Riga", "Vilnius"): True,   # directional: from Riga to Vilnius
        ("Vilnius", "Riga"): False,
        ("Vilnius", "Milan"): True,
        ("Milan", "Vilnius"): True,
        ("Riga", "Lisbon"): True,
        ("Lisbon", "Riga"): True,
        ("Milan", "Lisbon"): True,
        ("Lisbon", "Milan"): True
    }
    
    # Our chosen itinerary order (one possible optimal itinerary meeting all constraints and direct flight rules):
    # Sequence of cities: Vienna -> Rome -> Riga -> Vilnius -> Milan -> Lisbon -> Oslo
    # Flights will occur on the transition day, meaning the destination and origin share that day.
    itinerary_order = [
        ("Vienna", requirements["Vienna"]),
        ("Rome", requirements["Rome"]),
        ("Riga", requirements["Riga"]),
        ("Vilnius", requirements["Vilnius"]),
        ("Milan", requirements["Milan"]),
        ("Lisbon", requirements["Lisbon"]),
        ("Oslo", requirements["Oslo"])
    ]
    
    # To satisfy the overlapping day count, if there are N segments,
    # we have N - 1 flight days where the same day counts for two cities.
    # Total days needed = sum(required_days) - (N - 1)
    # Our chosen ordering: sum = 4+3+2+4+2+3+3 = 21, and flight overlaps = 6, giving 15 days total.
    # We now assign day ranges for each city such that:
    # - The first city gets its full range, ending on its last day.
    # - Each subsequent city starts on the same day as the flight from the previous city (overlap).
    
    segments = []
    current_day = 1
    # For the first city, assign its days:
    city, req = itinerary_order[0]
    start_day = current_day
    end_day = start_day + req - 1  # no overlap needed for the first city's start
    segments.append({"day_range": f"{start_day}-{end_day}", "place": city})
    current_day = end_day  # current_day is the day we depart (flight day in which we are already present in next city)
    
    # For each subsequent city, the flight day is the current_day (overlap day)
    for idx in range(1, len(itinerary_order)):
        city, req = itinerary_order[idx]
        # The flight day (current_day) counts for this new city.
        start_day = current_day
        # So additional days needed = req - 1; new end_day becomes:
        end_day = start_day + (req - 1)
        segments.append({"day_range": f"{start_day}-{end_day}", "place": city})
        current_day = end_day  # update current_day to departure day for next flight
    
    # At this point, segments should cover exactly 15 days.
    
    # Now we can check the special constraints:
    # Vienna must have day1 and day4. Our Vienna segment is from day1 to day4.
    # Lisbon must include a day between 11 and 13. Lisbon segment computed:
    # Lisbon segment: day_range from ? (it will be computed from the itinerary_order order.)
    # Oslo must include a day between 13 and 15.
    # Let's assert these conditions.
    def parse_range(day_range):
        s, e = day_range.split("-")
        return int(s), int(e)
    
    # For the cities with special date conditions, check if the city segment includes any day from the specified range.
    checks = []
    for seg in segments:
        city = seg["place"]
        if city in special:
            s, e = parse_range(seg["day_range"])
            days = set(range(s, e + 1))
            if not days.intersection(set(special[city])):
                checks.append(f"City {city} does not meet its special day constraint.")
    if checks:
        raise Exception("Itinerary does not meet special constraints: " + "; ".join(checks))
    
    # Check direct flight connectivity between successive cities.
    for i in range(len(itinerary_order) - 1):
        city_from = itinerary_order[i][0]
        city_to = itinerary_order[i+1][0]
        if not flights.get((city_from, city_to), False):
            raise Exception(f"No direct flight from {city_from} to {city_to}")
    
    # Output the itinerary in JSON format: only day_range and place.
    output = segments
    print(json.dumps(output, indent=4))

if __name__ == "__main__":
    main()