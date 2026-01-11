import itertools
import json

# Cities and required days
cities = ["Reykjavik", "Riga", "Warsaw", "Istanbul", "Krakow"]
required_days = {
    "Reykjavik": 7,
    "Riga": 2,
    "Warsaw": 3,
    "Istanbul": 6,
    "Krakow": 7
}

# Direct flights
direct_flights = {
    ("Istanbul", "Krakow"),
    ("Warsaw", "Reykjavik"),
    ("Istanbul", "Warsaw"),
    ("Riga", "Istanbul"),
    ("Krakow", "Warsaw"),
    ("Riga", "Warsaw")
}
# Make it undirected
for a, b in list(direct_flights):
    direct_flights.add((b, a))

# Special constraints
def check_constraints(itinerary):
    # itinerary: list of tuples (city, start_day, end_day inclusive)
    # Check Riga includes day 1 or day 2
    riga_ok = False
    for city, start, end in itinerary:
        if city == "Riga":
            if start <= 2 <= end:
                riga_ok = True
            break  # Riga appears only once
    if not riga_ok:
        return False
    
    # Check Istanbul includes some of days 2–7
    istanbul_ok = False
    for city, start, end in itinerary:
        if city == "Istanbul":
            if not (end < 2 or start > 7):  # overlap with [2,7]
                istanbul_ok = True
            break
    if not istanbul_ok:
        return False
    
    return True

# Generate all permutations of cities
valid_itineraries = []

for perm in itertools.permutations(cities):
    # Check direct flights between consecutive cities
    valid_path = True
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in direct_flights:
            valid_path = False
            break
    if not valid_path:
        continue
    
    # Now assign days
    # We have 21 days total, 5 cities, 4 travel days (each travel day counted twice)
    # Let's try to assign required days with travel days as overlaps
    # We start day 1 in first city, stay required_days[city] days, but last day in city overlaps with next city's first day if we travel that day.
    # Actually simpler: Let stay_days = required_days, but travel days are extra days in both cities.
    # So total calendar days = sum(stay_days) - (num_flights) because each travel day reduces calendar by 1? Let's derive:
    # Total city-days = sum(stay_days) + num_flights (since each travel day adds 1 extra)
    # Calendar days = total city-days - num_flights = sum(stay_days) = 25? That's wrong, we know calendar days = 21.
    # Let's do concrete:
    # Day 1 in A, stay a days, then travel day a+1 to B, day a+1 counts for A and B.
    # So A gets a+1 days, B starts day a+1.
    # So if we have stays S1, S2, S3, S4, S5, then:
    # City1: days 1..S1 (S1 days), travel day S1+1
    # City2: days S1+1..S1+S2 (S2 days), travel day S1+S2+1
    # etc.
    # But then last city ends at day S1+S2+S3+S4+S5.
    # That sum = 25, but we want 21. So we must reduce each stay by 1 except first? No, travel days are counted in both, so:
    # Actually: Calendar days = S1 + S2 + S3 + S4 + S5 - (num_flights) because each travel day is counted in previous city's stay? Let's just brute-force numeric assignment.

    # Let's brute-force start days:
    # We have 5 cities, 4 gaps (travel days). Let required = [7,2,3,6,7]
    # Start day1 = 1.
    # Day in city i = start[i] to end[i], end[i] = start[i] + required[i] - 1? No, because travel day is last day in city i and first day in city i+1.
    # So: start[0] = 1
    # end[0] = start[0] + required[0] - 1? No, because travel day is extra. Let's do:
    # stay_actual[i] = required[i]
    # start[i+1] = start[i] + stay_actual[i]
    # Then end[i] = start[i+1] - 1
    # Then total calendar days = start[4] + required[4] - 1
    # We want total = 21.
    # So start[4] = 22 - required[4] = 15.
    # We can solve for start times.
    
    # Let's just search for start days:
    required = [required_days[c] for c in perm]
    
    # start[0] = 1
    # start[i] = start[i-1] + required[i-1] for i=1..4
    # Then total days = start[4] + required[4] - 1
    # This gives total = 1 + sum(required) - 1 = sum(required) = 25, too many.
    # So we must subtract 4 from sum(required) to get 21. That means each travel day reduces stay in one city? Actually travel day is extra in both, so it doesn't reduce stay.
    # This is tricky. Let's instead explicitly model:
    
    # Let’s try: City1: days 1..d1, travel day d1+1, City2: days d1+1..d2, travel day d2+1, etc.
    # Then City1 gets days 1..d1+1? No, travel day d1+1 is in City1 and City2.
    # So City1 gets days 1..d1+1, but d1+1 is also start of City2.
    # Then City2 gets days d1+1..d2+1, etc.
    # Then required[i] = (d_i - start_i + 1) + 1? Too messy.
    
    # Better: Let’s just brute-force start and end days with small search.
    
    # We know sum(required) = 25, calendar days = 21, so 4 travel days double-counted.
    # So each travel day is an overlap between two cities.
    # So schedule: start1=1, end1=start1+R1-1 + 1? Let's do example:
    # If R1=2, R2=3, with 1 travel day overlap:
    # City1: day1, day2 (travel day2 to City2), City2: day2, day3, day4.
    # Then City1 has 2 days, City2 has 3 days, calendar days=4.
    # So formula: end[i] = start[i] + required[i] - 1 + (1 if i < 4 else 0)? No.
    
    # Let's search integer start days:
    # start[0] = 1
    # for i in 0..3: end[i] = start[i] + required[i] - 1 + 1 (the +1 is travel day overlap)
    # start[i+1] = end[i]
    # end[4] = start[4] + required[4] - 1
    # total_days = end[4]
    # We want total_days = 21.
    
    start = [0]*5
    end = [0]*5
    start[0] = 1
    for i in range(4):
        end[i] = start[i] + required[i] - 1 + 1  # +1 for travel overlap
        start[i+1] = end[i]
    end[4] = start[4] + required[4] - 1
    total = end[4]
    
    if total == 21:
        # Build itinerary
        itinerary = []
        for i in range(5):
            itinerary.append((perm[i], start[i], end[i]))
        if check_constraints(itinerary):
            valid_itineraries.append(itinerary)

# Take first valid itinerary
if valid_itineraries:
    itinerary = valid_itineraries[0]
    result = {"itinerary": []}
    for city, start, end in itinerary:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        result["itinerary"].append({"day_range": day_range, "place": city})
    
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}, indent=2))