#!/usr/bin/env python3
import json

def compute_itinerary():
    # Input Parameters
    total_days = 17
    # Cities and required durations (including overlaps)
    # When flying from one city to the next, the flight day counts as a day in both cities.
    # So the effective sum is: (sum of durations) - (number of transitions) = total_days.
    # Given durations:
    # Nice: 3 days
    # Reykjavik: 2 days (must include meeting friend in days 3-4)
    # Stockholm: 2 days (must include meeting friend in days 4-5)
    # Split: 3 days
    # Copenhagen: 2 days
    # Venice: 4 days
    # Vienna: 3 days (must include workshop in days 11-13)
    # Porto: 5 days (wedding between days 13-17)
    #
    # Total days if simply summed = 3+2+2+3+2+4+3+5 = 24.
    # There will be 7 flight transitions, so effective days = 24 - 7 = 17.
    #
    # We must also obey direct flight connections.
    # Selected ordering that satisfies flight connectivity and meeting constraints:
    # Order chosen:
    # 1. Nice
    # 2. Reykjavik      (direct: Nice-Reykjavik)
    # 3. Stockholm      (direct: Reykjavik-Stockholm)
    # 4. Split          (direct: Stockholm-Split)
    # 5. Copenhagen     (direct: Split-Copenhagen)
    # 6. Venice         (direct: Copenhagen-Venice)
    # 7. Vienna         (direct: Venice-Vienna)
    # 8. Porto          (direct: Vienna-Porto)
    #
    # This ordering respects:
    # - Meeting in Reykjavik occurs on day 3 or 4 (Reykjavik days: see below).
    # - Meeting in Stockholm on day 4 or 5.
    # - Workshop in Vienna between day 11 and 13.
    # - Wedding in Porto between day 13 and 17.
    #
    # Direct flights in this ordering are:
    # Nice -> Reykjavik: available
    # Reykjavik -> Stockholm: available
    # Stockholm -> Split: available
    # Split -> Copenhagen: available
    # Copenhagen -> Venice: available
    # Venice -> Vienna: available
    # Vienna -> Porto: available

    # Define cities in order along with their required durations.
    itinerary_plan = [
        {"place": "Nice", "duration": 3},
        {"place": "Reykjavik", "duration": 2},
        {"place": "Stockholm", "duration": 2},
        {"place": "Split", "duration": 3},
        {"place": "Copenhagen", "duration": 2},
        {"place": "Venice", "duration": 4},
        {"place": "Vienna", "duration": 3},
        {"place": "Porto", "duration": 5},
    ]
    # The total sum of durations is 24.
    # Number of transitions (flights) = len(itinerary_plan) - 1 = 7.
    # Effective total days = 24 - 7 = 17. This matches the trip requirement.

    # Now, compute the day ranges:
    # First city: starts at day 1, ends at day (start + duration - 1)
    # Next city: its start day = previous city's end day (flight day, counted in both)
    itinerary_output = []
    current_day = 1
    for idx, segment in enumerate(itinerary_plan):
        start_day = current_day
        end_day = start_day + segment["duration"] - 1
        # Append the result for the current city in the itinerary
        itinerary_output.append({
            "day_range": f"{start_day}-{end_day}",
            "place": segment["place"]
        })
        # For next segment, the flight day is overlapping so new start equals current end_day.
        current_day = end_day

    # Convert to JSON dictionary with key "itinerary"
    result = {"itinerary": itinerary_output}
    return result

if __name__ == '__main__':
    itinerary = compute_itinerary()
    # Output JSON formatted result
    print(json.dumps(itinerary))