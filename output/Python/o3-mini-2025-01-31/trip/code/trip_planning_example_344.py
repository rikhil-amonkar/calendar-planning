#!/usr/bin/env python3
import json

def compute_itinerary():
    # Input parameters (can be adjusted as needed)
    total_days = 20

    # Required effective days for each city.
    required_days = {
        "Valencia": 6,
        "Athens": 6,
        "Naples": 5,
        "Zurich": 6
    }
    
    # Special constraints:
    # - Visit relatives in Athens between day 1 and day 6, so Athens must be early.
    # - Attend a wedding in Naples between day 16 and day 20, so Naples must be late.
    #
    # Direct flight connectivity (bidirectional unless indicated otherwise):
    #   - Valencia <-> Naples
    #   - Valencia -> Athens    (thus, for our planning, we do not use Athens -> Valencia)
    #   - Athens <-> Naples
    #   - Zurich <-> Naples
    #   - Athens <-> Zurich
    #   - Zurich <-> Valencia
    #
    # To satisfy these constraints and ensure connections, we choose the ordering:
    #   Athens -> Zurich -> Valencia -> Naples
    # This ordering places Athens first (satisfies relatives constraint) and Naples last (satisfies wedding constraint),
    # and every consecutive pair has a direct flight.
    
    itinerary_order = ["Athens", "Zurich", "Valencia", "Naples"]
    
    # The method for counting effective days:
    # Whenever you fly from city A to city B on day X, that day counts for both A and B.
    # Thus, if there are k flights between segments (k = number_of_cities - 1), then the sum of effective days is:
    #   total_effective = sum(required_days[city] for city in itinerary_order)
    # and the actual total days planned is: total_effective - k.
    # Here: 6 + 6 + 6 + 5 - 3 = 20, which matches total_days.
    
    flight_count = len(itinerary_order) - 1
    
    # Now we assign day ranges.
    # For the first city: you start on day 1 and must accumulate its full effective days.
    # For subsequent cities: the first day is the overlap flight day (arriving on the day you depart the previous city).
    # So the effective days in each subsequent city = 1 (overlap day) + pure days.
    # Pure days for a city (except the last one) = required_days[city] - 1.
    # For the last city, you simply add the remaining days.
    
    segments = []
    current_day = 1
    
    # For the first city (Athens)
    current_city = itinerary_order[0]
    effective = required_days[current_city]
    # We plan to leave this city on its last effective day for the flight (if not the only city)
    start_day = current_day
    end_day = current_day + effective - 1  # this day is also departure day (overlap)
    segments.append({
        "day_range": f"{start_day}-{end_day}",
        "place": current_city
    })
    current_day = end_day  # flight day overlaps with both cities
    
    # For intermediate cities (except the last one)
    for city in itinerary_order[1:-1]:
        current_city = city
        effective = required_days[current_city]
        # current_day is already the overlap day from previous city
        # so add the remaining effective days - 1
        pure = effective - 1
        start_day = current_day  # overlap day already counted
        end_day = current_day + pure
        segments.append({
            "day_range": f"{start_day}-{end_day}",
            "place": current_city
        })
        current_day = end_day  # next flight day (overlap)
    
    # For the last city:
    current_city = itinerary_order[-1]
    effective = required_days[current_city]
    # Overlap day is current_day, then add the rest days.
    pure = effective - 1
    start_day = current_day
    end_day = current_day + pure
    segments.append({
        "day_range": f"{start_day}-{end_day}",
        "place": current_city
    })
    # current_day = end_day  (should equal total_days)
    
    # Validate that our plan spans the correct number of days
    if end_day != total_days:
        raise ValueError("Computed itinerary does not match total planned days.")
    
    return segments

if __name__ == "__main__":
    itinerary = compute_itinerary()
    # Output JSON formatted itinerary (list of dictionaries with day_range and place)
    print(json.dumps(itinerary))