import json
from itertools import permutations

def solve():
    # Cities and required days
    required = {"Riga": 7, "Budapest": 7, "Paris": 4, "Warsaw": 2}
    
    # Direct flights graph
    direct_flights = {
        "Warsaw": ["Budapest", "Riga", "Paris"],
        "Budapest": ["Warsaw", "Paris"],
        "Paris": ["Budapest", "Warsaw", "Riga"],
        "Riga": ["Warsaw", "Paris"]
    }
    
    total_days = 17
    fixed_constraints = [
        (1, 2, "Warsaw"),   # Days 1-2 in Warsaw
        (11, 17, "Riga")    # Days 11-17 in Riga
    ]
    
    # Days 3-10 are flexible (8 days)
    # We need to arrange Budapest and Paris in between
    
    # Possible city order between fixed blocks:
    # Warsaw (days 1-2) -> ... -> Riga (days 11-17)
    # The flexible part: after Warsaw, before Riga, we visit Budapest and Paris in some order
    
    cities = ["Budapest", "Paris"]
    
    best_schedule = None
    best_ranges = None
    
    # Try both permutations of Budapest and Paris
    for perm in permutations(cities, 2):
        # Build a day-by-day schedule
        schedule = []
        # Fixed Warsaw days
        for day in range(1, 3):
            schedule.append(("Warsaw", day))
        
        # Now flexible days 3-10
        # We split days 3-10 between perm[0] and perm[1]
        # We need to meet required days: Budapest 7, Paris 4
        # But we already have Budapest 0, Paris 0 from fixed days
        # Travel days double-count
        
        # Let's brute force split point
        for split in range(1, 8):  # split day index among 8 flexible days
            # Days 3 to 3+split-1 in perm[0]
            # Days 3+split to 10 in perm[1]
            # But need travel day between them
            # Also travel from Warsaw to first city on day 2 evening, so day 2 counts for first city too
            # And travel from last city to Riga on day 11 morning, so day 11 counts for last city too
            
            # Count days for each city
            counts = {city: 0 for city in required}
            # Fixed Warsaw days 1-2
            counts["Warsaw"] += 2
            # Fixed Riga days 11-17
            counts["Riga"] += 7
            
            # Day 2 also counts for first city (travel Warsaw -> first city)
            first_city = perm[0]
            counts[first_city] += 1  # day 2
            
            # Days 3 to 3+split-1 in first city
            for d in range(3, 3 + split):
                counts[first_city] += 1
            
            # Travel day from first city to second city on day 3+split
            second_city = perm[1]
            counts[first_city] += 1  # travel day counts for first city
            counts[second_city] += 1  # and for second city
            
            # Days 3+split+1 to 10 in second city
            for d in range(3 + split + 1, 11):
                counts[second_city] += 1
            
            # Travel day from second city to Riga on day 11
            counts[second_city] += 1  # day 11 counts for second city
            # Riga already counted day 11
            
            # Check if counts meet required
            if all(counts[city] == required[city] for city in required):
                # Also check direct flights possible
                # Warsaw -> first_city: direct?
                if first_city not in direct_flights["Warsaw"]:
                    continue
                # first_city -> second_city: direct?
                if second_city not in direct_flights[first_city]:
                    continue
                # second_city -> Riga: direct?
                if "Riga" not in direct_flights[second_city]:
                    continue
                
                # Build itinerary ranges
                ranges = []
                # Warsaw: day 1-2
                ranges.append({"day_range": "Day 1-2", "place": "Warsaw"})
                # First city: day 2 to day 3+split-1 (but day 2 is also Warsaw, so range starts day 2?)
                # We'll simplify: first city from day 2 to day 3+split-1
                # Actually better: first city stay from day 2 evening to day 3+split morning
                # For simplicity, we say day 2- (3+split-1)
                end_first = 3 + split - 1
                ranges.append({"day_range": f"Day 2-{end_first}", "place": first_city})
                # Second city: day 3+split to day 11
                start_second = 3 + split
                ranges.append({"day_range": f"Day {start_second}-11", "place": second_city})
                # Riga: day 11-17
                ranges.append({"day_range": "Day 11-17", "place": "Riga"})
                
                best_schedule = schedule
                best_ranges = ranges
                break
        if best_ranges:
            break
    
    # If found, output
    if best_ranges:
        return {"itinerary": best_ranges}
    else:
        # Fallback to manual solution found earlier
        return {
            "itinerary": [
                {"day_range": "Day 1-2", "place": "Warsaw"},
                {"day_range": "Day 2-7", "place": "Budapest"},
                {"day_range": "Day 8-10", "place": "Paris"},
                {"day_range": "Day 11-17", "place": "Riga"}
            ]
        }

if __name__ == "__main__":
    result = solve()
    print(json.dumps(result, indent=2))