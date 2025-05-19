#!/usr/bin/env python3
import json

def main():
    # Input variables: city durations (required individual days) and constraints.
    # Note: The total individual days sum: 2 (Prague) + 4 (Helsinki) + 4 (Naples) + 3 (Frankfurt) + 3 (Lyon) = 16.
    # With 4 flights overlapping (each overlap counts in both cities), the actual trip duration is 16 - 4 = 12 days.
    duration_prague = 2    # Must also include a workshop between day1 and day2.
    duration_helsinki = 4  # Must cover the annual show from day2 to day5.
    duration_naples = 4
    duration_frankfurt = 3
    duration_lyon = 3

    # The allowed direct flights (edges in the flight graph):
    # Prague <-> Lyon, Prague <-> Frankfurt, Frankfurt <-> Lyon,
    # Helsinki <-> Naples, Helsinki <-> Frankfurt, Naples <-> Frankfurt, Prague <-> Helsinki.
    # Feasible itinerary order that meets both connectivity and constraints:
    # Start at Prague (to attend the workshop between day1 and day2),
    # then fly from Prague to Helsinki (direct flight available) for the annual show.
    # Next, fly from Helsinki to Naples (direct flight available),
    # then Naples to Frankfurt,
    # and finally from Frankfurt to Lyon.
    itinerary = [
        {"city": "Prague", "duration": duration_prague},
        {"city": "Helsinki", "duration": duration_helsinki},
        {"city": "Naples", "duration": duration_naples},
        {"city": "Frankfurt", "duration": duration_frankfurt},
        {"city": "Lyon", "duration": duration_lyon}
    ]

    # Calculate the actual itinerary day ranges.
    # If one flies from city A to city B on day X, that day counts for both A and B.
    # So, for the first city we start at day 1.
    # For each subsequent city, the start day is the same as the flight day from the previous city,
    # i.e. the end day (which is the overlapping flight day).
    day = 1
    result = []
    for idx, segment in enumerate(itinerary):
        city = segment["city"]
        duration = segment["duration"]
        # Calculate the end day for this city segment.
        end_day = day + duration - 1
        day_range = f"{day}-{end_day}"
        result.append({"day_range": day_range, "place": city})
        # Set the next start day equal to the current segment's end day (overlap flight day) unless this is the final city.
        day = end_day

    # Output the itinerary as a JSON-formatted dictionary (list of segments)
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()