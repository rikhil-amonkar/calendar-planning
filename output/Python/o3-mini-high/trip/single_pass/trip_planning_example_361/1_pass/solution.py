#!/usr/bin/env python3
import json
import itertools

def main():
    # Input variables and constraints
    total_days = 15
    required_days = {
        "Madrid": 7,    # Must be in Madrid for 7 days (and attend show from Day 1-7)
        "Paris": 6,     # Must stay in Paris for 6 days
        "Bucharest": 2, # Must visit Bucharest for 2 days (relatives on Day 14-15)
        "Seville": 3    # Must visit Seville for 3 days
    }
    # Direct flight connections (bidirectional)
    allowed_flights = {
        ("Paris", "Bucharest"), ("Bucharest", "Paris"),
        ("Seville", "Paris"), ("Paris", "Seville"),
        ("Madrid", "Bucharest"), ("Bucharest", "Madrid"),
        ("Madrid", "Paris"), ("Paris", "Madrid"),
        ("Madrid", "Seville"), ("Seville", "Madrid")
    }
    
    # The cities to visit (must be exactly 4 cities)
    cities = ["Madrid", "Paris", "Bucharest", "Seville"]
    
    # Fixed starting and ending cities due to constraints:
    # - Annual show: must be in Madrid from Day 1 to Day 7, so Madrid is first.
    # - Relatives: Bucharest on Day 14-15, so Bucharest is last.
    start_city = "Madrid"
    end_city = "Bucharest"
    
    # The remaining cities (middle segments)
    middle_cities = [city for city in cities if city not in [start_city, end_city]]
    
    valid_schedule = None
    
    # Try all orders for the middle cities and check flight connectivity and scheduling.
    for perm in itertools.permutations(middle_cities):
        order = [start_city] + list(perm) + [end_city]
        # Check if consecutive flights exist in the itinerary order
        valid_order = True
        for i in range(len(order) - 1):
            if (order[i], order[i+1]) not in allowed_flights:
                valid_order = False
                break
        if not valid_order:
            continue

        # Build the schedule with overlapping flight days.
        # Rule: When flying from city A to city B on day X, day X is counted for both.
        itinerary = []
        current_day = 1
        for idx, city in enumerate(order):
            d = required_days[city]
            if idx == 0:
                # First segment: assign full d days starting from current_day.
                start_day = current_day
                end_day = start_day + d - 1
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                current_day = end_day  # flight departure happens at the end of this day
            else:
                # For subsequent segments, the arrival flight day is the same as current_day.
                start_day = current_day  # arrival day (overlap with previous segment's flight day)
                end_day = start_day + d - 1
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                current_day = end_day
        # Check if the computed itinerary fits the total actual days.
        if current_day == total_days:
            # Verify fixed constraints: Madrid must be Day 1-7 and Bucharest must be Day 14-15.
            if itinerary[0]["day_range"] == "Day 1-7" and itinerary[-1]["day_range"] == "Day 14-15":
                valid_schedule = itinerary
                break

    # Output the result as a JSON-formatted dictionary.
    output = {"itinerary": valid_schedule}
    print(json.dumps(output))

if __name__ == "__main__":
    main()