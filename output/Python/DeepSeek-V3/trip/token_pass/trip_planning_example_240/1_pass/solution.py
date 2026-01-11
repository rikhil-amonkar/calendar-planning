import json
from itertools import product

def is_direct_flight(c1, c2):
    direct_flights = {
        ("Berlin", "Tallinn"),
        ("Tallinn", "Berlin"),
        ("Prague", "Tallinn"),
        ("Tallinn", "Prague"),
        ("Stockholm", "Tallinn"),
        ("Tallinn", "Stockholm"),
        ("Prague", "Stockholm"),
        ("Stockholm", "Prague"),
        ("Stockholm", "Berlin"),
        ("Berlin", "Stockholm")
    }
    return (c1, c2) in direct_flights or c1 == c2

def solve():
    cities = ["Prague", "Berlin", "Tallinn", "Stockholm"]
    required = {"Prague": 2, "Berlin": 3, "Tallinn": 5, "Stockholm": 5}
    
    # Fixed days: index 0 = day 1
    # day 6 -> index 5, day 8 -> index 7, days 9-12 -> indices 8-11
    fixed = {
        5: ("Berlin", "Berlin"),   # day 6
        7: ("Berlin", "Berlin"),   # day 8
        8: ("Tallinn", "Tallinn"), # day 9
        9: ("Tallinn", "Tallinn"), # day 10
        10: ("Tallinn", "Tallinn"), # day 11
        11: ("Tallinn", "Tallinn")  # day 12
    }
    
    # Remaining days: 0,1,2,3,4,6 (day 7)
    remaining_indices = [0, 1, 2, 3, 4, 6]
    
    # Generate all possibilities for remaining days
    # Each day: (morn, eve) with morn, eve in cities
    # But to reduce search, note: if morn != eve, need direct flight
    # Also, consecutive days need direct flight from prev eve to curr morn
    
    best_solution = None
    
    # We'll brute force over all possibilities (4^12 is huge, but we fix many days)
    # Actually, we have 6 days, each day (morn, eve) in 4*4=16 combos, but many invalid if morn!=eve and no direct flight
    # Precompute valid pairs for a day
    valid_pairs = []
    for c1 in cities:
        for c2 in cities:
            if c1 == c2 or is_direct_flight(c1, c2):
                valid_pairs.append((c1, c2))
    
    # For remaining indices, we try all combos
    for combo in product(valid_pairs, repeat=len(remaining_indices)):
        # Build full schedule
        schedule = [None] * 12
        for idx, day_idx in enumerate(remaining_indices):
            schedule[day_idx] = combo[idx]
        # Fill fixed days
        for day_idx, pair in fixed.items():
            schedule[day_idx] = pair
        
        # Check consecutive days flight connectivity
        valid = True
        for d in range(11):
            eve_city = schedule[d][1]
            next_morn_city = schedule[d+1][0]
            if eve_city != next_morn_city and not is_direct_flight(eve_city, next_morn_city):
                valid = False
                break
        if not valid:
            continue
        
        # Count days per city
        counts = {city: 0 for city in cities}
        for morn, eve in schedule:
            counts[morn] += 1
            if eve != morn:
                counts[eve] += 1
        
        # Check totals
        if all(counts[city] == required[city] for city in cities):
            # Found valid schedule
            best_solution = schedule
            break
    
    if best_solution is None:
        return {"error": "No valid itinerary found"}
    
    # Convert to itinerary format: group consecutive days with same (morn, eve)
    itinerary = []
    day = 1
    while day <= 12:
        start = day
        morn, eve = best_solution[day-1]
        if morn == eve:
            place = morn
            # extend while same city and no travel
            while day <= 12 and best_solution[day-1] == (morn, eve):
                day += 1
            end = day - 1
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": place})
        else:
            # travel day
            # We split into two entries: first city in morning, second in evening
            # But note: they might want combined representation. We'll just show as travel day.
            # According to problem, day counts for both cities, so we can list it as two entries or one.
            # We'll do one entry: "Day X: City A to City B"
            itinerary.append({"day_range": f"Day {day}", "place": f"{morn} to {eve}"})
            day += 1
    
    # Post-process to merge consecutive same-place entries
    merged = []
    i = 0
    while i < len(itinerary):
        current = itinerary[i]
        j = i + 1
        while j < len(itinerary) and itinerary[j]["place"] == current["place"] and "to" not in current["place"]:
            j += 1
        if j > i + 1:
            # merge from i to j-1
            start_day = int(itinerary[i]["day_range"].split()[1].split("-")[0])
            end_day = int(itinerary[j-1]["day_range"].split("-")[-1])
            merged.append({"day_range": f"Day {start_day}-{end_day}", "place": current["place"]})
        else:
            merged.append(current)
        i = j
    
    return {"itinerary": merged}

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))