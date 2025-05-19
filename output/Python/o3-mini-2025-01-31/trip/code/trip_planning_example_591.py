#!/usr/bin/env python3
import json

def compute_itinerary():
    # Total trip days
    total_days = 17

    # Cities and their required stay durations (including flight overlap counts)
    # Note: if a flight happens on a day, that day counts for both the departure and arrival city.
    # Durations from constraints:
    # Geneva: 4 days (with relatives between day 1 and day 4)
    # Munich: 7 days (with friends meeting between day 4 and day 10)
    # Bucharest: 2 days
    # Valencia: 6 days
    # Stuttgart: 2 days
    # The sum of days if counted separately would be 4+7+2+6+2 = 21.
    # Since we have 5 cities (i.e. 4 flight transitions), each flight day is counted twice.
    # To fit into 17 total days, we must overlap exactly 4 days (one per flight).
    #
    # The available direct flights are:
    #   Geneva <-> Munich, Munich <-> Valencia, Bucharest <-> Valencia, Munich <-> Bucharest,
    #   Valencia <-> Stuttgart, Geneva <-> Valencia.
    #
    # In order to satisfy the relative meeting constraint in Geneva between day 1 and day 4,
    # and the friend meeting in Munich between day 4 and day 10, a valid order is:
    #   Geneva -> Munich -> Bucharest -> Valencia -> Stuttgart
    # Check connectivity:
    #   Geneva -> Munich: exists.
    #   Munich -> Bucharest: exists.
    #   Bucharest -> Valencia: exists.
    #   Valencia -> Stuttgart: exists.
    #
    # With flight overlap, the itinerary is:
    #   Geneva: Day 1 to Day 4 (4 days)
    #   Munich: Day 4 to Day 10 (7 days, day 4 is overlap)
    #   Bucharest: Day 10 to Day 11 (2 days, day 10 is overlap)
    #   Valencia: Day 11 to Day 16 (6 days, day 11 is overlap)
    #   Stuttgart: Day 16 to Day 17 (2 days, day 16 is overlap)
    
    # Define cities and their durations.
    itinerary_data = [
        {"place": "Geneva", "duration": 4},
        {"place": "Munich", "duration": 7},
        {"place": "Bucharest", "duration": 2},
        {"place": "Valencia", "duration": 6},
        {"place": "Stuttgart", "duration": 2}
    ]
    
    # Calculate itinerary schedule using flight overlap logic:
    schedule = []
    current_day = 1
    for city in itinerary_data:
        # The city time range starts at current_day and ends at current_day + duration - 1.
        start_day = current_day
        end_day = current_day + city["duration"] - 1
        schedule.append({
            "day_range": f"{start_day}-{end_day}",
            "place": city["place"]
        })
        # For next flight, assume flight on the last day: arrival is counted on that same day.
        # Therefore, the next city's start_day is the same as the current end_day.
        current_day = end_day
    
    # Verify that the final day equals the total trip days
    if current_day != total_days:
        raise ValueError(f"Computed itinerary does not fill the required {total_days} days (ends on day {current_day}).")
    
    return schedule

def main():
    itinerary = compute_itinerary()
    # Output the itinerary as JSON-format (only day_range and place information)
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()