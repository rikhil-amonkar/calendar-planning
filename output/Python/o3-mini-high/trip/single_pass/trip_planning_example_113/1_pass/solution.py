#!/usr/bin/env python3
import json

def compute_itinerary():
    # Trip constraints
    total_trip_days = 12
    days_naples = 3
    days_milan = 7
    days_seville = 4
    show_start_day = 9  # Seville annual show starts on day 9
    show_end_day = 12   # Seville annual show ends on day 12

    # Direct flight routes available
    # Only these two pairs of cities have direct flights:
    # Milan <-> Seville and Naples <-> Milan.
    direct_flights = {("Naples", "Milan"), ("Milan", "Naples"),
                      ("Milan", "Seville"), ("Seville", "Milan")}

    # We need to visit three cities: Naples, Milan, and Seville.
    # To satisfy the flight constraints, the itinerary order must be:
    # Naples -> Milan -> Seville.
    itinerary_order = [("Naples", days_naples),
                         ("Milan", days_milan),
                         ("Seville", days_seville)]

    # Validate that consecutive cities are connected by direct flights.
    for i in range(len(itinerary_order) - 1):
        from_city = itinerary_order[i][0]
        to_city = itinerary_order[i+1][0]
        if (from_city, to_city) not in direct_flights:
            return {"error": f"No direct flight from {from_city} to {to_city}."}

    # Calculate flight transitions.
    # Note: When flying from city A to city B on day X, that day counts for both A and B.
    # Total occupancy days = sum(city_days) - (# flight transitions).
    # To match the total trip days, we need exactly 2 flight transitions:
    # (3 + 7 + 4) - 2 = 12.
    required_flight_transitions = (days_naples + days_milan + days_seville) - total_trip_days
    if required_flight_transitions != 2:
        return {"error": "Trip constraints do not allow a valid itinerary with the required overlaps."}

    # Compute the day ranges.
    itinerary = []
    current_day = 1
    for idx, (city, duration) in enumerate(itinerary_order):
        start_day = current_day
        end_day = start_day + duration - 1
        # If this is not the last segment then the last day is used as a flight day
        if idx < len(itinerary_order) - 1:
            current_day = end_day  # Next city starts on the same day (flight day overlap)
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})

    # Ensure that the Seville segment covers the annual show dates.
    # The Seville portion must include days 9 to 12.
    for segment in itinerary:
        if segment["place"] == "Seville":
            # Extract start and end days from the day_range string.
            parts = segment["day_range"].replace("Day ", "").split("-")
            seg_start, seg_end = int(parts[0]), int(parts[1])
            if seg_start > show_start_day or seg_end < show_end_day:
                return {"error": "The Seville stay does not cover the annual show dates."}
    return {"itinerary": itinerary}

def main():
    plan = compute_itinerary()
    print(json.dumps(plan))

if __name__ == "__main__":
    main()