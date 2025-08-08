#!/usr/bin/env python3
import json
import itertools

def main():
    # Input trip constraints
    total_days = 9
    # Required days in each city
    city_durations = {
        "Vienna": 2,     # Also needed for workshop between day 1-2
        "Nice": 2,
        "Stockholm": 5,
        "Split": 3      # Also must host conferences on day 7 and day 9
    }

    # Allowed direct flight connections (bidirectional)
    direct_flights = {
        ("Vienna", "Stockholm"),
        ("Vienna", "Nice"),
        ("Vienna", "Split"),
        ("Stockholm", "Split"),
        ("Nice", "Stockholm")
    }
    # Build a set with both directions.
    allowed = set()
    for (a, b) in direct_flights:
        allowed.add((a, b))
        allowed.add((b, a))
    
    # Special day constraints:
    workshop_days = {1, 2}  # Must be in Vienna on at least one of these days.
    conference_days = {7, 9}  # Must be in Split on these days.
    
    # We model the trip as a sequence of segments.
    # Each segment has a fixed duration. Consecutive segments overlap on the transition day.
    # Total trip days = (sum of segment durations) - (number of transitions)
    # Since 4 segments have 3 transitions, we must have:
    #   2 (Vienna) + 2 (Nice) + 5 (Stockholm) + 3 (Split) - 3 = 9 days.
    #
    # The itinerary must visit every city and obey the flight connections.
    # In addition, the workshop constraint forces the Vienna segment
    # to be at the very start (to cover day 1 and/or day 2).
    
    first_city = "Vienna"
    remaining_cities = [city for city in city_durations if city != first_city]
    
    valid_itinerary = None
    # Try all orders for the remaining three cities.
    for perm in itertools.permutations(remaining_cities):
        itinerary_order = [first_city] + list(perm)
        durations = [city_durations[city] for city in itinerary_order]
        
        # Compute segments as a list of dicts.
        # The rule is: the first segment starts on day 1 and runs for d1 days.
        # Then each subsequent segment starts on the day the previous segment ended.
        segments = []
        current_day = 1
        for city, d in zip(itinerary_order, durations):
            # The segment runs from current_day to current_day + d - 1.
            seg = {"city": city, "start": current_day, "end": current_day + d - 1}
            segments.append(seg)
            current_day = seg["end"]  # next segment starts on the overlapping transition day
        
        # Check overall trip day count.
        if segments[-1]["end"] != total_days:
            continue
        
        # Check direct flight connectivity between consecutive segments.
        flight_ok = True
        for i in range(len(segments) - 1):
            from_city = segments[i]["city"]
            to_city = segments[i+1]["city"]
            if (from_city, to_city) not in allowed:
                flight_ok = False
                break
        if not flight_ok:
            continue
        
        # Workshop: The first segment must be Vienna and cover day 1-2.
        first_seg_days = set(range(segments[0]["start"], segments[0]["end"] + 1))
        if segments[0]["city"] != "Vienna" or not (first_seg_days & workshop_days):
            continue
        
        # Conference: For each required conference day, check that at least one segment
        # for Split covers that day.
        conf_ok = True
        for day in conference_days:
            found = False
            for seg in segments:
                if seg["city"] == "Split" and seg["start"] <= day <= seg["end"]:
                    found = True
                    break
            if not found:
                conf_ok = False
                break
        if not conf_ok:
            continue
        
        # If we reach here, we have found a valid itinerary.
        valid_itinerary = segments
        break

    # Prepare the JSON output structure.
    output = {"itinerary": []}
    if valid_itinerary is not None:
        for seg in valid_itinerary:
            day_range = "Day {}-{}".format(seg["start"], seg["end"])
            # The itinerary segments might overlap, which is intended as per flight rule.
            output["itinerary"].append({"day_range": day_range, "place": seg["city"]})
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()