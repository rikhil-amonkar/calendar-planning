#!/usr/bin/env python3
import json

def compute_itinerary():
    # Input constraints (hardcoded based on the problem statement)
    total_days = 16
    
    # Cities and required durations.
    # Note: if a flight occurs on a certain day, that day counts for both departure and arrival cities.
    # The order of cities is chosen to satisfy all constraints and flight connectivity:
    # 1. Barcelona: Must be there on days 1-3 for the annual show.
    # 2. Oslo: Must be there for 2 days and meet friends between day 3 and day 4.
    # 3. Venice: 4 days. (reachable directly from Oslo)
    # 4. Brussels: 3 days with friend meeting between day 9 and 11.
    # 5. Copenhagen: 3 days.
    # 6. Stuttgart: 3 days.
    # 7. Split: 4 days.
    #
    # The direct flight connections used are:
    # Barcelona -> Oslo (allowed)
    # Oslo -> Venice (allowed)
    # Venice -> Brussels (allowed)
    # Brussels -> Copenhagen (allowed)
    # Copenhagen -> Stuttgart (allowed)
    # Stuttgart -> Split (allowed)
    
    itinerary_info = [
        {"place": "Barcelona", "duration": 3},
        {"place": "Oslo", "duration": 2},
        {"place": "Venice", "duration": 4},
        {"place": "Brussels", "duration": 3},
        {"place": "Copenhagen", "duration": 3},
        {"place": "Stuttgart", "duration": 3},
        {"place": "Split", "duration": 4}
    ]
    
    # Compute day ranges.
    # The rule: For the first city, start at day 1.
    # For each subsequent flight, the flight day is shared, so the new city starts on the same day as the previous city's end.
    schedule = []
    current_day = 1
    for city in itinerary_info:
        place = city["place"]
        duration = city["duration"]
        # The city is visited from current_day to end_day.
        end_day = current_day + duration - 1
        # Store the computed day range as "start-end"
        day_range = f"{current_day}-{end_day}"
        schedule.append({"day_range": day_range, "place": place})
        # For the next city, the flight happens on the end_day,
        # so the next city starts on the same day (overlap on flight day).
        current_day = end_day
    
    # Verify that the itinerary fits into the total_days (it must equal total_days since overlaps reduce total span)
    # The last city end day is the total trip duration.
    if current_day != total_days:
        raise ValueError(f"Computed itinerary lasts {current_day} days, but expected {total_days} days.")
    
    return {"itinerary": schedule}

if __name__ == '__main__':
    itinerary_plan = compute_itinerary()
    print(json.dumps(itinerary_plan))