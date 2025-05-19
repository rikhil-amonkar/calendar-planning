#!/usr/bin/env python3
import json

def main():
    # Input parameters (constraints)
    total_days = 23

    # Cities and their required total days (note: flight days count for both adjacent cities)
    required_days = {
        "Geneva": 7,   # and must be in Geneva on day 1 and day 7 (conference)
        "Porto": 7,
        "Paris": 6,
        "Reykjavik": 2,
        "Oslo": 5     # plus must visit relatives in Oslo between day 19 and day 23
    }
    
    # Direct flight connections (both directions):
    # Using set of frozensets for undirected connection checking.
    flights = {
        frozenset(["Paris", "Oslo"]),
        frozenset(["Geneva", "Oslo"]),
        frozenset(["Porto", "Paris"]),
        frozenset(["Geneva", "Paris"]),
        frozenset(["Geneva", "Porto"]),
        frozenset(["Paris", "Reykjavik"]),
        frozenset(["Reykjavik", "Oslo"]),
        frozenset(["Porto", "Oslo"])
    }
    
    # We must visit all 5 cities, and there are extra scheduling constraints:
    # - Day 1 and day 7 conference in Geneva so Geneva must be the first city.
    # - Oslo must be visited late enough such that a portion falls between day 19 and day 23.
    #   In our scheduling Oslo will be the final segment.
    # - Also, from Geneva the next city must be directly connected.
    #
    # After some analysis one valid ordering is:
    # S1: Geneva (7 days)      -- covers conference on day 1 and day 7.
    # S2: Porto (7 days)       -- flight: Geneva -> Porto is direct.
    # S3: Paris (6 days)       -- flight: Porto -> Paris is direct.
    # S4: Reykjavik (2 days)   -- flight: Paris -> Reykjavik is direct.
    # S5: Oslo (5 days)        -- flight: Reykjavik -> Oslo is direct, and Oslo covers day 19-23.
    #
    # Check flights between consecutive cities:
    # Geneva -> Porto: frozenset(["Geneva", "Porto"]) in flights -> True
    # Porto -> Paris: frozenset(["Porto", "Paris"]) in flights -> True
    # Paris -> Reykjavik: frozenset(["Paris", "Reykjavik"]) in flights -> True
    # Reykjavik -> Oslo: frozenset(["Reykjavik", "Oslo"]) in flights -> True
    
    itinerary_order = ["Geneva", "Porto", "Paris", "Reykjavik", "Oslo"]
    
    # To fit in exactly 23 unique days, we plan the itinerary segments so that
    # when flying from one city to the next, the flight day counts for both cities.
    # For the first segment we use all days as unique.
    # For each subsequent segment, the flight day is shared with the previous segment.
    #
    # Thus if a segment requires d days, it contributes (d - 1) unique extra days,
    # except the first which contributes d days.
    #
    # Let's compute the unique day counts along the itinerary:
    unique_days_used = 0
    segments = []
    for i, city in enumerate(itinerary_order):
        d = required_days[city]
        if i == 0:
            # first segment, uses full d unique days
            start_day = 1
            end_day = start_day + d - 1
            unique_days_used = d
        else:
            # subsequent segment: flight day overlaps the last day of previous segment.
            # So it adds d - 1 unique days.
            start_day = segments[-1]["end_day"]  # same as the previous end day
            end_day = start_day + (d - 1)
            unique_days_used += (d - 1)
        segments.append({
            "place": city,
            "start_day": start_day,
            "end_day": end_day,
            "required": d
        })
    
    # Check that we used exactly the total number of unique days (should equal 23)
    if unique_days_used != total_days:
        raise ValueError(f"Unique days used ({unique_days_used}) does not match total days ({total_days})")
    
    # Prepare the final JSON output with only the day ranges and corresponding place.
    result = []
    for seg in segments:
        day_range = f"{seg['start_day']}-{seg['end_day']}"
        result.append({"day_range": day_range, "place": seg["place"]})
    
    # Output the JSON-formatted itinerary
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()