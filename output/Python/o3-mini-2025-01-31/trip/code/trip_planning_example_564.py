#!/usr/bin/env python3
import json

def compute_itinerary():
    # Input constraints
    total_days = 16

    # Cities and planned durations (including the flight overlap rule)
    # Each city has an "allocated" duration.
    # Overlap rule: For cities after the first, the first day counts as the flight day from previous city.
    # Order is chosen based on available direct flights and constraints:
    #   Seville -> Rome -> Istanbul -> Naples -> Santorini
    # Flight connections:
    #   Seville-Rome, Rome-Istanbul, Istanbul-Naples, Naples-Santorini are all valid.
    #
    # Duration constraints for each city (as required visit durations):
    # Istanbul: 2 days; must cover day 6 and day 7 (relatives visit).
    # Rome: 3 days.
    # Seville: 4 days.
    # Naples: 7 days.
    # Santorini: 4 days; must cover day 13 to day 16 (wedding).
    cities = [
        ("Seville", 4),
        ("Rome", 3),
        ("Istanbul", 2),
        ("Naples", 7),
        ("Santorini", 4)
    ]
    
    # We'll assign day ranges obeying the rule that when flying on a day,
    # that day is included in the durations of BOTH cities.
    # The actual timeline will be computed as:
    #   first city: days = start to start + duration - 1
    #   subsequent cities: start day = previous city end day, end day = start + duration - 1
    itinerary = []
    
    current_day = 1
    for index, (city, duration) in enumerate(cities):
        if index == 0:
            start_day = current_day
            end_day = start_day + duration - 1
        else:
            # For subsequent cities, we overlap the flight day with the previous city's last day.
            start_day = itinerary[-1]['end_day']
            end_day = start_day + duration - 1
        itinerary.append({
            "place": city,
            "start_day": start_day,
            "end_day": end_day
        })
        current_day = end_day + 1  # for reference, though not used

    # Verification of specific constraints:
    # Istanbul must include days 6 and 7.
    # Find Istanbul itinerary segment:
    istanbul_segment = next(seg for seg in itinerary if seg["place"] == "Istanbul")
    if not (istanbul_segment["start_day"] <= 6 <= istanbul_segment["end_day"] and
            istanbul_segment["start_day"] <= 7 <= istanbul_segment["end_day"]):
        raise ValueError("Istanbul segment does not cover days 6 and 7 for the relatives visit.")
    
    # Santorini must include wedding days between day 13 and day 16.
    santorini_segment = next(seg for seg in itinerary if seg["place"] == "Santorini")
    if not (santorini_segment["start_day"] <= 13 and santorini_segment["end_day"] >= 16):
        raise ValueError("Santorini segment does not cover days 13 to 16 for the wedding.")

    # Sum up actual total days:
    # Using the rule, total actual days = first city duration + sum(each subsequent city duration - 1)
    computed_total_days = cities[0][1] + sum(d - 1 for _, d in cities[1:])
    if computed_total_days != total_days:
        raise ValueError(f"Computed total days ({computed_total_days}) does not match required total_days ({total_days}).")
    
    # Prepare JSON-formatted output with only "day_range" and "place".
    result = []
    for seg in itinerary:
        day_range = f"{seg['start_day']}-{seg['end_day']}"
        result.append({
            "day_range": day_range,
            "place": seg["place"]
        })
    
    return result

def main():
    itinerary = compute_itinerary()
    # Output the result as JSON-formatted dictionary (list of segments).
    print(json.dumps(itinerary))

if __name__ == '__main__':
    main()