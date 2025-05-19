import json

def compute_itinerary():
    # Trip constraints and parameters
    # Cities with required durations (days of stay required)
    # If a flight is taken on a given day, that day counts for both the departure and arrival cities.
    # Order chosen based on available direct flights:
    # Dubrovnik -> Helsinki -> Reykjavik -> Prague -> Valencia -> Porto
    cities = [
        {"place": "Dubrovnik", "days": 4},
        {"place": "Helsinki", "days": 4},
        {"place": "Reykjavik", "days": 4},
        {"place": "Prague", "days": 3},
        {"place": "Valencia", "days": 5},
        {"place": "Porto", "days": 3}
    ]
    total_trip_days = 18

    # The idea:
    # When departing from one city to the next, the flight day is shared by both cities.
    # Thus if a city has "d" booked days, the last day is used as the flight day leaving for the next city (if any).
    # We can compute the itinerary by starting at day 1 for the first city,
    # and for each subsequent city, the start day equals the previous city's end day.
    itinerary = []
    current_day = 1
    for index, city in enumerate(cities):
        # The city stays for city['days'] days.
        # We count the day of arrival (which might be the same as the previous city's departure).
        start_day = current_day
        end_day = start_day + city["days"] - 1
        itinerary.append({
            "day_range": f"{start_day}-{end_day}",
            "place": city["place"]
        })
        # For the next city, we assume flight occurs on the arrival day (overlap)
        current_day = end_day

    # At this point, our computed end day should match the specified total_trip_days.
    # We add a check and adjust if necessary.
    if current_day != total_trip_days:
        # If there is a mismatch, adjust the last city's end day accordingly.
        # Compute the difference (this difference should equal the sum of overlapping flight days)
        diff = total_trip_days - current_day
        # Adjust the last city's day range's end_day
        last_entry = itinerary[-1]
        start, end = last_entry["day_range"].split("-")
        new_end = int(end) + diff
        last_entry["day_range"] = f"{start}-{new_end}"
        current_day = new_end

    return itinerary

if __name__ == "__main__":
    itinerary = compute_itinerary()
    # Output the result as a JSON formatted string containing only day_range and place.
    print(json.dumps(itinerary))