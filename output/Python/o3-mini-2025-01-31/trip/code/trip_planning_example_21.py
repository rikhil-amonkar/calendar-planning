#!/usr/bin/env python3
import json

def main():
    # Input parameters
    total_days = 10
    venice_required_days = 6
    workshop_window = (5, 10)  # workshop in Venice must be between day 5 and 10
    mykonos_required_days = 2
    vienna_required_days = 4

    # Direct flight connections (graph)
    direct_flights = {
        "Mykonos": ["Vienna"],
        "Vienna": ["Mykonos", "Venice"],
        "Venice": ["Vienna"]
    }
    
    # We choose the only valid sequence given the available direct flights:
    # Mykonos -> Vienna -> Venice
    # We need to determine the flight days such that:
    # 1. Mykonos days (with flight overlap counted) = mykonos_required_days
    # 2. Vienna days (including flight overlapping both before and after) = vienna_required_days
    # 3. Venice days = venice_required_days = total_days - flight_day_2 + 1
    
    # Let x be the flight day from Mykonos to Vienna. Then days in Mykonos = x.
    # We want: x = mykonos_required_days.
    x = mykonos_required_days  # Flight day from Mykonos -> Vienna is day 2.
    
    # Let y be the flight day from Vienna to Venice.
    # Days in Vienna = y - x + 1, so:
    # y - x + 1 = vienna_required_days --> y = vienna_required_days + x - 1.
    y = vienna_required_days + x - 1  # For x=2, y = 4 + 2 - 1 = 5.
    
    # Days in Venice = total_days - y + 1
    venice_days = total_days - y + 1
    
    # Check if Venice meets the required days:
    if venice_days != venice_required_days:
        raise ValueError("Cannot allocate days to Venice as required.")
    
    # Additionally, ensure that the Venice visit period overlaps with the workshop window.
    # Venice is visited from day y to day total_days.
    if not (workshop_window[0] >= y and workshop_window[0] <= total_days) and not (workshop_window[1] >= y and workshop_window[1] <= total_days):
        raise ValueError("Venice itinerary does not cover the required workshop window.")

    # The computed itinerary is as follows:
    # - Mykonos: from day 1 to day x
    # - Vienna: from day x to day y (day x and day y count in both cities due to flights)
    # - Venice: from day y to day total_days

    itinerary = [
        {"day_range": f"1-{x}", "place": "Mykonos"},
        {"day_range": f"{x}-{y}", "place": "Vienna"},
        {"day_range": f"{y}-{total_days}", "place": "Venice"}
    ]
    
    # Output the result as JSON-formatted dictionary (list of dicts)
    print(json.dumps(itinerary, indent=4))

if __name__ == "__main__":
    main()