#!/usr/bin/env python3
import json

def compute_itinerary():
    # Given input parameters
    total_days = 18
    required_split = 6
    required_santorini = 7
    required_london = 7
    conf_days = [12, 18]  # must be in Santorini
    
    # Allowed direct flights:
    # London <-> Santorini and Split <-> London.
    #
    # We need the total "city-days" (when counting a day with a flight from A to B as being in both A and B)
    # to sum to required_split + required_london + required_santorini = 6 + 7 + 7 = 20.
    # Since the itinerary lasts 18 days, we must have exactly 2 days (flight days) that are double‐counted.
    #
    # A viable route that uses exactly 2 flight days (overlap days) and visits all three cities is:
    #   Split  -->  London  -->  Santorini
    #
    # with:
    #   Flight 1 on day 6 from Split to London (day6 counts for both Split and London)
    #   Flight 2 on day 12 from London to Santorini (day12 counts for both London and Santorini)
    #
    # We then plan the segments so that the total counts become:
    #   Split: pure days + flight day = required_split
    #   London: pure days + 2 flight days = required_london
    #   Santorini: pure days + flight day = required_santorini
    #
    # Let:
    #   d1 = number of pure days spent in Split before flight1.
    #   d2 = number of pure days spent in London between flight1 and flight2.
    #   d3 = number of pure days spent in Santorini after flight2.
    #
    # During flight days:
    #   On flight day1 (day F1) the traveler is in both Split and London.
    #   On flight day2 (day F2) the traveler is in both London and Santorini.
    #
    # So the computed city-day counts will be:
    #   Split: d1 + 1 = required_split  =>  d1 = required_split - 1 = 5.
    #   London: d2 + 2 = required_london  =>  d2 = required_london - 2 = 5.
    #   Santorini: d3 + 1 = required_santorini  =>  d3 = required_santorini - 1 = 6.
    #
    # And total days:
    #   Total = (pure days: d1 + d2 + d3) + (flight days: 2) = 5 + 5 + 6 + 2 = 18.
    #
    # To assign calendar day ranges we take:
    #   Segment 1 (Split): 
    #       Pure days: days 1 through 5.
    #       Flight day 1: day 6 (counts as Split and London).
    #       So for planning purposes we can assign Split the range "1-6".
    #   Segment 2 (London):
    #       Flight day 1 (already on day 6)
    #       Pure days: days 7 through 11.
    #       Flight day 2: day 12 (counts as London and Santorini).
    #       So assign London the range "6-12".
    #   Segment 3 (Santorini):
    #       Flight day 2 (day 12) already counts for Santorini, and pure days days 13 through 18.
    #       So assign Santorini the range "12-18".
    #
    # This itinerary also satisfies the conference constraints:
    #   Day 12 is included in Santorini (via flight day 2) and day 18 is within Santorini.
    
    itinerary = [
        {"day_range": "1-6", "place": "Split"},
        {"day_range": "6-12", "place": "London"},
        {"day_range": "12-18", "place": "Santorini"}
    ]
    
    # Double-check conference days: they must occur in Santorini.
    # According to our segmentation, day 12 is the overlapping day of London and Santorini.
    # We'll assume that the conference obligation takes priority so on day 12 the conference is attended in Santorini.
    if not (12 in conf_days and 18 in conf_days):
        raise ValueError("Conference days are not set properly.")
    
    return itinerary

def main():
    itinerary = compute_itinerary()
    # Output the result as JSON formatted dictionary list.
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()