#!/usr/bin/env python3
import json

def compute_itinerary():
    # Input trip constraints as variables.
    total_days = 20

    # Define each city with its required duration (in days)
    # Note: Overlap occurs at flight days.
    # The itinerary order (must follow available direct flight connections):
    # Berlin -> Barcelona -> Lyon -> Nice -> Stockholm -> Athens -> Vilnius
    # This order satisfies mandatory events:
    # - Berlin: 3 days (includes conference on day1 and day3)
    # - Barcelona: 2 days (includes workshop between day3 and day4, by flying on day3 from Berlin to Barcelona)
    # - Lyon: 2 days (includes wedding between day4 and day5, by flying on day4 from Barcelona to Lyon)
    # - Nice: 5 days
    # - Stockholm: 5 days
    # - Athens: 5 days
    # - Vilnius: 4 days
    #
    # Overlap rule: When flying on the same day, the flight day is counted in both the origin and destination.
    # We simulate this by letting the start day of each subsequent city equal the end day of the previous city.
    segments = [
        {"place": "Berlin", "duration": 3},
        {"place": "Barcelona", "duration": 2},
        {"place": "Lyon", "duration": 2},
        {"place": "Nice", "duration": 5},
        {"place": "Stockholm", "duration": 5},
        {"place": "Athens", "duration": 5},
        {"place": "Vilnius", "duration": 4},
    ]

    # To ensure total calendar days is 20, we simulate the itinerary timeline.
    itinerary = []
    current_day = 1
    for seg in segments:
        # For the first segment the start day is current_day.
        start_day = current_day
        # The segment duration is counted such that the flight day (start day after the first segment) overlaps.
        # So if a segment requires D days, we count its days as:
        #   start_day, start_day+1, ... , start_day+(duration - 1)
        # And then for the next flight we set current_day = start_day + (duration - 1)
        end_day = start_day + seg["duration"] - 1
        itinerary.append({
            "day_range": f"{start_day}-{end_day}",
            "place": seg["place"]
        })
        # For subsequent segments, we plan the flight on the last day of the previous segment,
        # meaning that day is counted again in the new city.
        current_day = end_day

    # After assigning all segments, current_day is the final day in the itinerary.
    # We want the calendar span to be total_days.
    # To check, we can compute the calendar length:
    calendar_length = current_day
    if calendar_length != total_days:
        # Adjust if needed (should not happen with our chosen ordering).
        difference = total_days - calendar_length
        # Add extra days to the last city if needed.
        last_seg = itinerary[-1]
        start, end = map(int, last_seg["day_range"].split('-'))
        new_end = end + difference
        itinerary[-1]["day_range"] = f"{start}-{new_end}"
    
    return itinerary

if __name__ == '__main__':
    plan = compute_itinerary()
    # Output the itinerary as JSON formatted dictionary list.
    # Each dictionary contains only "day_range" and "place".
    print(json.dumps(plan, indent=2))