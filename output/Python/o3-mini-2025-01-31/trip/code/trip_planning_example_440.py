import json

def main():
    # Input parameters
    total_days = 12
    
    # Cities and required durations for each (with overlaps on flight days)
    # The "required_durations" here add up to 6+2+3+2+3 = 16 days.
    # Since each flight day (for 4 flights) counts for both cities, the overall days equals 16 - 4 = 12.
    required_durations = {
        "Geneva": 6,     # Must spend 6 days in Geneva (note: Geneva has a direct flight to Split)
        "Split": 2,      # Must spend 2 days in Split
        "Vilnius": 3,    # Must spend 3 days in Vilnius (relatives visit between day 7 and day 9)
        "Helsinki": 2,   # Must spend 2 days in Helsinki
        "Reykjavik": 3   # Must spend 3 days in Reykjavik (wedding between day 10 and day 12)
    }
    
    # Flight connection ordering that satisfies the direct flights constraint:
    # Geneva -> Split, Split -> Vilnius, Vilnius -> Helsinki, Helsinki -> Reykjavik.
    cities_order = ["Geneva", "Split", "Vilnius", "Helsinki", "Reykjavik"]
    
    # The itinerary is computed with overlapping days on flight days.
    # If you fly from city A to city B on day X, then day X counts for both cities.
    itinerary = []
    
    # Start at day 1.
    current_day = 1
    
    # For each city in the itinerary, calculate the day range.
    # The first day of each segment (except the very first) is the same as the flight day from the previous city.
    for city in cities_order:
        duration = required_durations[city]
        # The segment end day is current_day + duration - 1.
        end_day = current_day + duration - 1
        itinerary.append({
            "day_range": f"{current_day}-{end_day}",
            "place": city
        })
        # For the next city, the flight is done on the last day of the current city,
        # so the next city "starts" on the same day due to the overlapping flight.
        current_day = end_day

    # Output the itinerary as JSON with only the day_range and place fields.
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()