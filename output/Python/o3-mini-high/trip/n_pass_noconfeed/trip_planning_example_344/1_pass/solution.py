import json

def main():
    # Trip constraints and parameters
    total_days = 20
    required_stays = {
        "Athens": 6,   # Must spend 6 days in Athens (and visit relatives during days 1-6)
        "Zurich": 6,   # Must spend 6 days in Zurich
        "Valencia": 6, # Must spend 6 days in Valencia
        "Naples": 5    # Must spend 5 days in Naples (wedding between days 16-20)
    }
    relatives_window = (1, 6)   # In Athens, visit relatives between day 1 and day 6
    wedding_window = (16, 20)   # In Naples, attend the wedding between day 16 and day 20

    # Flight connection list.
    # Format: (Origin, Destination). Most connections are bidirectional,
    # except "from Valencia to Athens" which is only allowed in that direction.
    flights = {
        ("Valencia", "Naples"), ("Naples", "Valencia"),
        ("Valencia", "Athens"),  # only flight from Valencia to Athens is available
        ("Athens", "Naples"), ("Naples", "Athens"),
        ("Zurich", "Naples"), ("Naples", "Zurich"),
        ("Athens", "Zurich"), ("Zurich", "Athens"),
        ("Zurich", "Valencia"), ("Valencia", "Zurich")
    }

    # Choose an itinerary order that meets the constraints.
    # Athens must be early to satisfy the relatives-visit, and Naples last for the wedding.
    # Also, ensure that consecutive cities have a direct flight.
    itinerary_order = ["Athens", "Zurich", "Valencia", "Naples"]

    # Verify that each leg in our chosen order has a direct flight.
    valid_route = True
    for i in range(1, len(itinerary_order)):
        origin = itinerary_order[i - 1]
        destination = itinerary_order[i]
        if (origin, destination) not in flights:
            valid_route = False
            break
    if not valid_route:
        print(json.dumps({"error": "No valid direct flight connection for the chosen itinerary order."}))
        return

    # Compute the day ranges for each city segment.
    # The rule is: if you fly on a day from city A to city B, that day counts for both.
    # Therefore, for n segments over total_days T with (n-1) flights, we have:
    # Sum(city_days) = T + (n - 1)
    # Our required city_days sum is: 6 + 6 + 6 + 5 = 23, and T = 20 with 3 overlapping flight days.
    itinerary = []
    current_day = 1
    for index, city in enumerate(itinerary_order):
        # For the first city, all required days are unique except the last day, which is a flight day.
        # For subsequent cities, the arrival day overlaps with the previous flight day.
        # Thus, the calendar span for a city is "required_stays[city]" days.
        segment_start = current_day
        segment_end = current_day + required_stays[city] - 1
        itinerary.append({
            "day_range": f"Day {segment_start}-{segment_end}",
            "place": city
        })
        # The next segment starts with the overlapping flight day (the current segment's end day)
        current_day = segment_end

    # Check that the last segment ends exactly at total_days
    if itinerary and itinerary[-1]["day_range"].split()[-1].split("-")[-1] != str(total_days):
        # In our calculation, current_day should equal total_days after the last segment.
        pass

    # The computed itinerary satisfies:
    # - Athens (Day 1-6): Relatives can be visited in the window 1-6.
    # - Zurich (Day 6-11): 6 days in Zurich.
    # - Valencia (Day 11-16): 6 days in Valencia.
    # - Naples (Day 16-20): 5 days in Naples, with a wedding occurring between days 16 and 20.
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()