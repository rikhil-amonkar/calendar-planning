#!/usr/bin/env python3
import json

def compute_itinerary():
    # Total trip days and city constraints (durations as specified)
    total_trip_days = 28
    
    # The itinerary order (cities and required durations):
    # Note: The overall planned durations sum to 37 days, but with 9 flight-day overlaps, the trip is 28 days.
    # The order is chosen to satisfy the following constraints:
    # - Naples (4 days) must cover day 5-8 (for visiting relatives)
    # - Athens (4 days) must cover day 8-11 (for the workshop)
    # - Copenhagen (5 days) must cover day 11-15 (for meeting a friend)
    # - Mykonos (2 days) must cover day 27-28 (for the conference)
    # And the order must obey direct flight connectivity.
    #
    # Chosen order with direct flight links:
    #   Prague -> Brussels -> Naples -> Athens -> Copenhagen -> Santorini -> Geneva -> Dubrovnik -> Munich -> Mykonos
    #
    # Check flight connections:
    #   Prague -> Brussels (direct)
    #   Brussels -> Naples (direct)
    #   Naples -> Athens (direct)
    #   Athens -> Copenhagen (direct)
    #   Copenhagen -> Santorini (direct)
    #   Santorini -> Geneva (direct)
    #   Geneva -> Dubrovnik (direct)
    #   Dubrovnik -> Munich (direct)
    #   Munich -> Mykonos (direct)
    
    cities = [
        {"place": "Prague", "duration": 2},
        {"place": "Brussels", "duration": 4},
        {"place": "Naples", "duration": 4},      # Must cover day 5-8 for relatives
        {"place": "Athens", "duration": 4},       # Must cover day 8-11 for workshop
        {"place": "Copenhagen", "duration": 5},   # Must cover day 11-15 for friend meeting
        {"place": "Santorini", "duration": 5},
        {"place": "Geneva", "duration": 3},
        {"place": "Dubrovnik", "duration": 3},
        {"place": "Munich", "duration": 5},
        {"place": "Mykonos", "duration": 2}       # Conference on day 27-28
    ]
    
    # The assumption is that when you fly from city A to city B on day X,
    # that day X counts in the duration of both A and B.
    # This means that the start day for the first city is day 1.
    # For subsequent cities, the start day will be equal to the end day of the previous city.
    # Let "start_day" be the first day present in a city and "end_day" the last day in that city.
    
    itinerary = []
    current_start = 1
    for city in cities:
        duration = city["duration"]
        # The city is visited for 'duration' days counting the overlapping flight day.
        # So the end_day = start_day + duration - 1.
        end_day = current_start + duration - 1
        itinerary.append({
            "day_range": f"{current_start}-{end_day}",
            "place": city["place"]
        })
        # For next city, because of flight overlap, the next city starts on the same day as the previous city's end.
        current_start = end_day
    
    return itinerary

if __name__ == "__main__":
    plan = compute_itinerary()
    # Output as JSON formatted string containing only day_range and place for each segment.
    print(json.dumps(plan, indent=4))