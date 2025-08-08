#!/usr/bin/env python3
import json

def main():
    # Trip constraints
    total_days = 16
    bucharest_required = 7  # Total days to spend in Bucharest
    lyon_required = 7       # Total days to spend in Lyon
    porto_required = 4      # Total days to spend in Porto
    wedding_window = (1, 7) # Wedding in Bucharest must occur between Day 1 and Day 7

    # Direct flight connections: Bucharest <-> Lyon, Lyon <-> Porto.
    # This forces the itinerary order to be: Bucharest -> Lyon -> Porto.
    itinerary_order = [
        ("Bucharest", bucharest_required),
        ("Lyon", lyon_required),
        ("Porto", porto_required)
    ]
    
    # When flying, the flight day counts for both the departure and arrival cities.
    # Thus, the unique day count is:
    #   total required days = sum(required_days) - (number of flights)
    flights = len(itinerary_order) - 1  # Two flights.
    computed_total = bucharest_required + lyon_required + porto_required - flights
    if computed_total != total_days:
        raise ValueError("The input constraints do not add up to the total trip days.")
    
    # Compute the itinerary segments.
    # For each segment, if a flight occurs on the day it ends, that same day is also the start for the next city.
    itinerary = []
    current_day = 1
    for city, required_days in itinerary_order:
        end_day = current_day + required_days - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        # Next segment starts on the same day as flight dual-count (overlap day)
        current_day = end_day

    # The wedding constraint is met because Bucharest is visited from Day 1 to Day 7,
    # ensuring the wedding (scheduled between Day 1 and Day 7) is attended.
    trip_plan = {"itinerary": itinerary}
    
    # Output the trip plan as a JSON-formatted dictionary.
    print(json.dumps(trip_plan))

if __name__ == "__main__":
    main()