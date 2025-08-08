#!/usr/bin/env python3
import json

def main():
    # Trip constraints
    total_days = 13
    required_days = {
        "Seville": 2,
        "Stuttgart": 7,
        "Porto": 3,
        "Madrid": 4
    }
    conference_days = [7, 13]  # Must attend conferences in Stuttgart on these days
    relatives_madrid_range = (1, 4)  # Must visit relatives in Madrid between day 1 and day 4

    # Allowed direct flights (bidirectional)
    allowed_flights = {
        frozenset(["Porto", "Stuttgart"]),
        frozenset(["Seville", "Porto"]),
        frozenset(["Madrid", "Porto"]),
        frozenset(["Madrid", "Seville"])
    }
    
    # Based on connectivity and constraints, the viable itinerary order is fixed:
    # Start in Madrid (to visit relatives early), then Seville, then Porto, and finally Stuttgart
    itinerary_order = ["Madrid", "Seville", "Porto", "Stuttgart"]
    
    # Check that each consecutive flight is allowed.
    for i in range(len(itinerary_order) - 1):
        if frozenset([itinerary_order[i], itinerary_order[i+1]]) not in allowed_flights:
            print(json.dumps({"error": "No valid itinerary found based on flight constraints."}))
            return

    # Calculate itinerary segments.
    # Rule: If you fly from city A to city B on day X, then day X counts for both cities.
    # We treat the first segment as starting on day 1 and each flight day (the segment's end)
    # is the starting day for the next city.
    itinerary_segments = []
    current_day = 1
    for city in itinerary_order:
        duration = required_days[city]
        # The end day for this city segment is current_day + duration - 1
        end_day = current_day + duration - 1
        itinerary_segments.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        # Next segment starts on the same day as the flight day (overlap)
        current_day = end_day

    # Validate conference constraint: Stuttgart segment must include day 7 and day 13.
    stuttgart_segment = itinerary_segments[-1]
    st_range = stuttgart_segment["day_range"].replace("Day ","").split("-")
    st_start, st_end = int(st_range[0]), int(st_range[1])
    if not (st_start <= conference_days[0] <= st_end and st_start <= conference_days[1] <= st_end):
        print(json.dumps({"error": "Conference days are not within Stuttgart segment."}))
        return

    # Validate relatives visit in Madrid: Madrid segment must cover at least one day between day 1 and day 4.
    madrid_segment = itinerary_segments[0]
    md_range = madrid_segment["day_range"].replace("Day ","").split("-")
    md_start, md_end = int(md_range[0]), int(md_range[1])
    if md_end < relatives_madrid_range[0] or md_start > relatives_madrid_range[1]:
        print(json.dumps({"error": "Madrid segment does not cover the relatives visit window."}))
        return

    # Validate total trip duration matches total_days.
    if itinerary_segments[-1]["day_range"].split("-")[1].strip() != str(total_days):
        # This simple check ensures the final day equals total_days.
        print(json.dumps({"error": "Total trip duration does not match the required 13 days."}))
        return

    result = {"itinerary": itinerary_segments}
    print(json.dumps(result))

if __name__ == '__main__':
    main()