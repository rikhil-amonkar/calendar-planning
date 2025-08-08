#!/usr/bin/env python3
import json

def main():
    # Input trip constraints
    total_days = 18
    required_split = 6      # Must spend 6 days in Split (effective days)
    required_london = 7     # Must spend 7 days in London (effective days)
    required_santorini = 7  # Must spend 7 days in Santorini (effective days)
    conference_days = [12, 18]  # Must be in Santorini on these days

    # Available direct flights:
    # Split <-> London and London <-> Santorini.
    # The only valid route that meets all constraints is: Split -> London -> Santorini.
    #
    # Note: If a flight occurs on a day X, that day counts for both cities.
    #
    # Let flight1_day be the day of the flight from Split to London.
    # Then effective days in Split = (flight1_day) because days 1 to flight1_day (inclusive)
    #   count toward Split.
    # Set:
    flight1_day = required_split  # So flight1_day = 6

    # Next, let flight2_day be the day of the flight from London to Santorini.
    # London effective days = (flight2_day - flight1_day + 1)
    # We require:
    #    (flight2_day - flight1_day + 1) = required_london
    flight2_day = flight1_day + required_london - 1  # flight2_day = 6 + 7 - 1 = 12

    # Santorini effective days = total_days - flight2_day + 1
    effective_santorini = total_days - flight2_day + 1
    if effective_santorini != required_santorini:
        raise ValueError("Trip constraints cannot be met with the given parameters.")

    # Check that conference days fall in Santorini.
    # On flight days, the traveler is in both cities. Since flight2_day = 12,
    # day 12 counts as being in Santorini. Also day 18 is in Santorini.
    if 12 not in conference_days or total_days not in conference_days:
        raise ValueError("Conference days must be in Santorini.")

    # Build the itinerary.
    # Segment 1: Stay in Split from Day 1 to flight1_day.
    #   (Day 6 is the flight day from Split to London and counts for both cities.)
    # Segment 2: Stay in London from flight1_day to flight2_day.
    #   (Day 6 counts as London from flight1 and Day 12 counts for London as flight2.)
    # Segment 3: Stay in Santorini from flight2_day to total_days.
    #   (Day 12 counts for Santorini from flight2 and Day 18 is the final day.)
    itinerary = [
        {"day_range": f"Day 1-{flight1_day}", "place": "Split"},
        {"day_range": f"Day {flight1_day}-{flight2_day}", "place": "London"},
        {"day_range": f"Day {flight2_day}-{total_days}", "place": "Santorini"}
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()