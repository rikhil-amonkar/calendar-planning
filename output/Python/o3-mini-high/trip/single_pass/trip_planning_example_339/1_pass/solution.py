#!/usr/bin/env python3
import json

def main():
    # Total trip days
    total_days = 17

    # City constraints (number of days required per city)
    # Note: Flight days count for both the departing and arriving cities.
    constraints = {
        "Warsaw": 2,
        "Budapest": 7,
        "Paris": 4,
        "Riga": 7
    }

    # Specific event constraints
    show_in_warsaw_window = (1, 2)   # Annual show in Warsaw between Day 1 and Day 2
    wedding_in_riga_window = (11, 17)  # Wedding in Riga between Day 11 and Day 17

    # Allowed direct flight connections (bidirectional)
    allowed_flights = {
        frozenset(["Warsaw", "Budapest"]),
        frozenset(["Warsaw", "Riga"]),
        frozenset(["Budapest", "Paris"]),
        frozenset(["Warsaw", "Paris"]),
        frozenset(["Paris", "Riga"])
    }

    # We propose the following visitation order based on constraints:
    # Start in Warsaw (for the show), then Budapest, then Paris, and finally Riga (for the wedding).
    itinerary_cities = ["Warsaw", "Budapest", "Paris", "Riga"]
    
    # Verify that each consecutive flight is allowed
    for i in range(len(itinerary_cities) - 1):
        if frozenset([itinerary_cities[i], itinerary_cities[i+1]]) not in allowed_flights:
            raise ValueError(f"No direct flight available between {itinerary_cities[i]} and {itinerary_cities[i+1]}.")

    # Compute itinerary segments with overlapping flight days.
    # Each segment will be represented as a block [start_day, end_day] for that city.
    segments = []
    current_day = 1
    for city in itinerary_cities:
        # If a city requires D days, and the arrival day is counted,
        # then the segment ends at (start_day + D - 1).
        duration = constraints[city]
        end_day = current_day + duration - 1
        segments.append({
            "city": city,
            "start_day": current_day,
            "end_day": end_day
        })
        # Next city starts on the same day as the end_day because that day includes the flight arrival.
        current_day = end_day

    # Validate that the itinerary spans the total trip days.
    if segments[-1]["end_day"] != total_days:
        raise ValueError("The computed itinerary does not sum up to the required 17 days.")

    # Check the wedding constraint in Riga.
    riga_segment = next(seg for seg in segments if seg["city"] == "Riga")
    # Ensure there is an overlap with the wedding window.
    if riga_segment["end_day"] < wedding_in_riga_window[0] or riga_segment["start_day"] > wedding_in_riga_window[1]:
        raise ValueError("The wedding in Riga does not fall within the Riga segment days.")

    # Check the Warsaw show constraint.
    warsaw_segment = next(seg for seg in segments if seg["city"] == "Warsaw")
    if warsaw_segment["start_day"] > show_in_warsaw_window[0] or warsaw_segment["end_day"] < show_in_warsaw_window[1]:
        raise ValueError("The Warsaw segment does not cover the annual show days.")

    # Build the output itinerary in the required JSON format.
    # Each segment's day range is formatted as "Day X-Y" where overlapping flight days appear in both segments.
    output_itinerary = []
    for seg in segments:
        day_range = f"Day {seg['start_day']}-{seg['end_day']}"
        output_itinerary.append({
            "day_range": day_range,
            "place": seg["city"]
        })

    result = {"itinerary": output_itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()