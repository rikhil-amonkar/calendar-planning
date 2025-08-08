#!/usr/bin/env python3
import json

def main():
    # Trip constraints and parameters
    TOTAL_TRIP_DAYS = 27

    # City durations (as planned, in days)
    # Note: Each flight day is counted double (departure and arrival),
    # so total itinerary = sum(durations) - (number of transitions) = 36 - 9 = 27 days.
    city_durations = {
        "Warsaw": 3,
        "Porto": 5,
        "Naples": 4,
        "Brussels": 3,
        "Split": 3,
        "Reykjavik": 5,
        "Amsterdam": 4,
        "Lyon": 3,
        "Helsinki": 4,
        "Valencia": 2
    }
    
    # Event constraints (each event must occur within the city's stay window)
    events = {
        "Porto": {"event": "workshop", "window": (1, 5)},
        "Amsterdam": {"event": "relatives visit", "window": (5, 8)},
        "Helsinki": {"event": "wedding", "window": (8, 11)},
        "Naples": {"event": "conference", "days": [17, 20]},
        "Brussels": {"event": "annual show", "window": (20, 22)}
    }
    
    # Direct flight connections (bidirectional)
    flight_edges = [
        ("Amsterdam", "Warsaw"),
        ("Helsinki", "Brussels"),
        ("Helsinki", "Warsaw"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Lyon"),
        ("Amsterdam", "Naples"),
        ("Amsterdam", "Reykjavik"),
        ("Naples", "Valencia"),
        ("Porto", "Brussels"),
        ("Amsterdam", "Split"),
        ("Lyon", "Split"),
        ("Warsaw", "Split"),
        ("Porto", "Amsterdam"),
        ("Helsinki", "Split"),
        ("Brussels", "Lyon"),
        ("Porto", "Lyon"),
        ("Reykjavik", "Warsaw"),
        ("Brussels", "Valencia"),
        ("Valencia", "Lyon"),
        ("Porto", "Warsaw"),
        ("Warsaw", "Valencia"),
        ("Amsterdam", "Helsinki"),
        ("Porto", "Valencia"),
        ("Warsaw", "Brussels"),
        ("Warsaw", "Naples"),
        ("Naples", "Split"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Reykjavik"),
        ("Amsterdam", "Valencia"),
        ("Naples", "Brussels")
    ]
    
    # Build a flight graph dictionary (bidirectional)
    flights = {}
    for (a, b) in flight_edges:
        flights.setdefault(a, set()).add(b)
        flights.setdefault(b, set()).add(a)
    
    # Based on the event timing and durations, one optimal itinerary order is determined.
    # The reasoning is as follows:
    # 1. Porto must cover days 1-5 to allow the workshop between day 1 and 5.
    # 2. Amsterdam is then best placed to cover days 5-8 to satisfy the relatives visit.
    # 3. Helsinki follows covering days 8-11 for the wedding.
    # 4. Next, placing Reykjavik (5 days) then Warsaw (3 days) allows Naples (4 days)
    #    to start exactly at day 17, so that the conference in Naples on day 17 and day 20 is met.
    # 5. Brussels must follow Naples (overlapping on day 20) to attend the annual show from day 20-22.
    # 6. The remaining cities (Valencia, Lyon, Split) must form the final three legs with proper flight connectivity.
    #
    # The chosen order is:
    #   1. Porto     (5 days: Day 1-5)
    #   2. Amsterdam (4 days: Day 5-8)
    #   3. Helsinki  (4 days: Day 8-11)
    #   4. Reykjavik (5 days: Day 11-15)
    #   5. Warsaw    (3 days: Day 15-17)
    #   6. Naples    (4 days: Day 17-20) -> Conference days 17 & 20 in Naples.
    #   7. Brussels  (3 days: Day 20-22) -> Annual show from day 20 to 22.
    #   8. Valencia  (2 days: Day 22-23)
    #   9. Lyon      (3 days: Day 23-25)
    #  10. Split     (3 days: Day 25-27)
    itinerary_order = [
        ("Porto", city_durations["Porto"]),
        ("Amsterdam", city_durations["Amsterdam"]),
        ("Helsinki", city_durations["Helsinki"]),
        ("Reykjavik", city_durations["Reykjavik"]),
        ("Warsaw", city_durations["Warsaw"]),
        ("Naples", city_durations["Naples"]),
        ("Brussels", city_durations["Brussels"]),
        ("Valencia", city_durations["Valencia"]),
        ("Lyon", city_durations["Lyon"]),
        ("Split", city_durations["Split"])
    ]
    
    # Validate flight connectivity between consecutive cities
    for i in range(len(itinerary_order) - 1):
        city_from = itinerary_order[i][0]
        city_to = itinerary_order[i+1][0]
        if city_to not in flights.get(city_from, set()):
            raise ValueError(f"No direct flight from {city_from} to {city_to}.")

    # Compute itinerary day ranges using the flight-day overlap rule.
    itinerary = []
    current_day = 1
    for city, duration in itinerary_order:
        start_day = current_day
        end_day = start_day + duration - 1
        # For next city, the departure/arrival day (end_day) is overlapped.
        current_day = end_day
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
    
    # Check that the overall trip spans the total trip days.
    if current_day != TOTAL_TRIP_DAYS:
        raise ValueError(f"Overall itinerary does not add up to {TOTAL_TRIP_DAYS} days (got {current_day}).")
    
    # (Optional) Validate that event time constraints are satisfied.
    # Calculate individual city stay day ranges in a dict.
    city_schedule = {}
    current_day = 1
    for city, duration in itinerary_order:
        start_day = current_day
        end_day = start_day + duration - 1
        city_schedule[city] = (start_day, end_day)
        current_day = end_day

    # Validate event constraints for Porto, Amsterdam, Helsinki, Naples, Brussels.
    porto_start, porto_end = city_schedule["Porto"]
    if not (porto_start <= events["Porto"]["window"][1] and porto_end >= events["Porto"]["window"][0]):
        raise ValueError("Porto does not satisfy the workshop window constraint.")
    
    ams_start, ams_end = city_schedule["Amsterdam"]
    if not (ams_start <= events["Amsterdam"]["window"][1] and ams_end >= events["Amsterdam"]["window"][0]):
        raise ValueError("Amsterdam does not satisfy the relatives visit constraint.")
    
    hels_start, hels_end = city_schedule["Helsinki"]
    if not (hels_start <= events["Helsinki"]["window"][1] and hels_end >= events["Helsinki"]["window"][0]):
        raise ValueError("Helsinki does not satisfy the wedding constraint.")
    
    nap_start, nap_end = city_schedule["Naples"]
    for d in events["Naples"]["days"]:
        if not (nap_start <= d <= nap_end):
            raise ValueError(f"Naples does not cover conference day {d}.")
    
    brus_start, brus_end = city_schedule["Brussels"]
    event_window = events["Brussels"]["window"]
    if not (brus_start <= event_window[1] and brus_end >= event_window[0]):
        raise ValueError("Brussels does not satisfy the annual show constraint.")

    # Prepare and output the final itinerary in JSON format.
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()