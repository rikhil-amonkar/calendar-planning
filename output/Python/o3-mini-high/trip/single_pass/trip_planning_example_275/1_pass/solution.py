#!/usr/bin/env python3
import json

def main():
    # Input constraints
    total_days = 14
    # Required visitation days for each city
    required_days = {
        "Vilnius": 4,
        "Split": 5,
        "Madrid": 6,
        "Santorini": 2
    }
    # Conference in Santorini must be attended on day 13 and day 14.
    conference_days = [13, 14]
    
    # Available direct flights:
    # Vilnius <-> Split, Split <-> Madrid, Madrid <-> Santorini
    # Thus, the only possible route is: Vilnius -> Split -> Madrid -> Santorini
    route = ["Vilnius", "Split", "Madrid", "Santorini"]
    
    # Using the rule that if you fly on day X, then you count as being in both departure and arrival cities on that day,
    # we can define flight days (transition days) as follows:
    # Let f1 be the flight day from Vilnius to Split.
    # Then Vilnius is visited from day 1 to day f1 (including flight day f1) and must equal required_days["Vilnius"].
    f1 = required_days["Vilnius"]  # Flight from Vilnius to Split on day f1.
    # For Split, arrival is on day f1 and departure (flight to Madrid) is on day f2.
    # Total days in Split = (f2 - f1 - 1 full days) + 2 (arrival day and departure day)
    # So, f2 can be determined by: f2 - f1 + 1 = required_days["Split"]
    f2 = f1 + required_days["Split"] - 1
    # Similarly, for Madrid, arriving on f2 and departing on f3 (flight to Santorini), 
    # total days in Madrid = f3 - f2 + 1 = required_days["Madrid"]
    f3 = f2 + required_days["Madrid"] - 1
    # For Santorini, arriving on f3 and staying until the end (day total_days),
    # total days counted = (total_days - f3) + 1. This must equal required_days["Santorini"].
    santorini_total = total_days - f3 + 1
    if santorini_total != required_days["Santorini"]:
        raise ValueError("The given constraints cannot be satisfied with the current parameters.")
    
    # Also ensure that the conference days (day 13 and day 14) are both spent in Santorini.
    if f3 > conference_days[0]:
        raise ValueError("Cannot attend the conference in Santorini on day 13 and day 14 with the computed schedule.")
    
    # Build the itinerary segments.
    # When flying, the flight day counts for both the departure and the arrival city.
    itinerary_segments = []
    # The segments are:
    # Vilnius: Day 1 to f1
    # Split: Day f1 to f2
    # Madrid: Day f2 to f3
    # Santorini: Day f3 to total_days
    flight_days = [f1, f2, f3]
    start_day = 1
    for i, city in enumerate(route):
        if i < len(flight_days):
            end_day = flight_days[i]
        else:
            end_day = total_days
        day_range = f"Day {start_day}-{end_day}"
        itinerary_segments.append({"day_range": day_range, "place": city})
        start_day = end_day  # Overlapping flight day becomes the start for the next city
    
    # Prepare final itinerary as a JSON dictionary.
    itinerary = {"itinerary": itinerary_segments}
    print(json.dumps(itinerary))

if __name__ == "__main__":
    main()