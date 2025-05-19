#!/usr/bin/env python3
import json

def main():
    # Input parameters (durations are planned stay days, not counting overlaps)
    total_days = 26
    # Planned stays (each city’s planned days if visited in isolation)
    planned = {
        "Lyon": 4,
        "Venice": 4,
        "Copenhagen": 4,
        "Barcelona": 3,
        "Dubrovnik": 5,
        "Athens": 2,
        "Reykjavik": 4,
        "Munich": 3,
        "Tallinn": 5,
    }
    # Critical time-window constraints:
    # - In Copenhagen, relatives must be met between day 7 and day 10.
    # - In Barcelona, friend meeting must happen between day 10 and day 12.
    # - In Dubrovnik, wedding takes place between day 16 and day 20.
    #
    # We choose an itinerary order that respects available direct flights and the scheduling windows.
    # After some analysis, one valid order (assuming direct flight connections work bidirectionally) is:
    #
    #  Order:
    #    1. Lyon          (no constraint, chosen as start)
    #    2. Venice        (fly from Lyon on day 4; direct flight: Lyon-Venice)
    #    3. Copenhagen    (fly from Venice on day 7; direct flight: Venice-Copenhagen)
    #         -> This stay exactly covers days 7-10, within the relatives window.
    #    4. Barcelona     (fly from Copenhagen on day 10; direct flight: Copenhagen-Barcelona)
    #         -> Occupies days 10-12, covering the friend meeting.
    #    5. Dubrovnik     (fly from Barcelona on day 12; direct flight: Barcelona-Dubrovnik)
    #         -> With a 5-day stay from day 12 to day 16, day 16 falls in the wedding window.
    #    6. Athens        (fly from Dubrovnik on day 16; direct flight: Athens-Dubrovnik)
    #         -> A 2-day stay from day 16 to day 17.
    #    7. Reykjavik     (fly from Athens on day 17; using the bidirectional leg corresponding to "from Reykjavik to Athens")
    #         -> A 4-day stay occupying days 17-20.
    #    8. Munich        (fly from Reykjavik on day 20; direct flight: Reykjavik-Munich)
    #         -> A 3-day stay occupying days 20-22.
    #    9. Tallinn       (fly from Munich on day 22; direct flight: Munich-Tallinn)
    #         -> A 5-day stay occupying days 22-26.
    #
    # Note on overlaps:
    # When flying on a given day X, that day counts toward both the city you are leaving and the one you are arriving in.
    # Therefore, if we add all planned days (which sum to 34) and subtract the 8 overlapping flight days (between 9 cities),
    # we get an effective total of 26 days.
    #
    # We now compute the day ranges sequentially:
    itinerary_order = [
        "Lyon",
        "Venice",
        "Copenhagen",
        "Barcelona",
        "Dubrovnik",
        "Athens",
        "Reykjavik",
        "Munich",
        "Tallinn",
    ]
    
    day = 1
    results = []
    # For each city, we assign a range.
    # The rule: the planned duration is the number of days counting arrival day and subsequent days.
    # But note that when leaving a city, the departure day is the overlap day (and thus also the arrival day of the next city).
    for i, city in enumerate(itinerary_order):
        duration = planned[city]
        # The city is occupied for "duration" days counting the arrival day.
        # The day range is from current day to (day + duration - 1).
        start_day = day
        end_day = day + duration - 1
        results.append({
            "day_range": f"{start_day}-{end_day}",
            "place": city
        })
        # For all but the last city, subtract one day because the departure day is shared.
        if i < len(itinerary_order) - 1:
            day = end_day  # The shared flight day; next city starts on the same day (overlap)
        else:
            day = end_day

    # Check total effective days:
    # Total planned days if simply summed = sum(planned.values()) = 34.
    # Overlap days = (# of transitions) = 8.
    # Effective total = 34 - 8 = 26.
    effective_total = sum(planned.values()) - (len(itinerary_order) - 1)
    assert effective_total == total_days, f"Effective days {effective_total} do not match total_days {total_days}"

    # Output the itinerary as JSON.
    print(json.dumps(results, indent=2))
    
if __name__ == "__main__":
    main()