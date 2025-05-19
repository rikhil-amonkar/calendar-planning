#!/usr/bin/env python3
import json

def main():
    # Input constraints as variables
    total_days = 7
    required_days_riga = 2
    required_days_amsterdam = 2
    required_days_mykonos = 5

    # Flight connectivity (only these direct flights are allowed)
    direct_flights = {
        ("Amsterdam", "Mykonos"),
        ("Mykonos", "Amsterdam"),
        ("Riga", "Amsterdam"),
        ("Amsterdam", "Riga"),
    }

    # Constraints on relative visits: Must be in Riga on day1 and day2 (for visiting relatives),
    # so we choose to begin in Riga.
    
    # The trick is that if one flies from one city to another on the same day, that day counts in both cities.
    # Therefore we plan to use the overlapping flight days to meet the required stays.
    #
    # Plan:
    #   - Day 1: Only in Riga.
    #   - Day 2: Still in Riga (fulfilling the required 2 days; including visiting relatives) and take a flight from Riga to Amsterdam.
    #   - Day 3: In Amsterdam (fulfilling the required 2 days for Amsterdam, as day2 and day3 count) and take a flight from Amsterdam to Mykonos.
    #   - Days 4-7: In Mykonos.
    #   Note: Since the flight on day2 counts for both Riga and Amsterdam and the flight on day3 counts for both Amsterdam and Mykonos,
    #         the resulting days-per-city are:
    #             Riga: Day 1 and Day 2 (2 days)
    #             Amsterdam: Day 2 and Day 3 (2 days)
    #             Mykonos: Day 3, 4, 5, 6, 7 (5 days)
    #
    # Check if the flights are allowed per the given direct flights:
    #   Riga -> Amsterdam : allowed.
    #   Amsterdam -> Mykonos : allowed.
    
    # Compute actual itinerary using above reasoning and logical checks.
    itinerary = []
    
    # Determine day ranges for each city.
    # Riga: Days 1 to 2.
    riga_start = 1
    riga_end = riga_start + required_days_riga - 1  # day1 and day2
    
    # Amsterdam: Overlap day with Riga flight day on day2 and require 2 days in Amsterdam.
    # We assume departure from Riga on day2 (so day2 counts for both) and then remain day3.
    amsterdam_start = riga_end  # day2 (overlap)
    amsterdam_end = amsterdam_start + required_days_amsterdam - 1  # day2 and day3
    
    # Mykonos: Overlap day with Amsterdam flight on day3 and then remain until day7.
    mykonos_start = amsterdam_end  # day3 (overlap)
    mykonos_end = total_days  # day7
    
    # Verify the durations:
    actual_days_riga = riga_end - riga_start + 1
    actual_days_amsterdam = amsterdam_end - amsterdam_start + 1
    actual_days_mykonos = mykonos_end - mykonos_start + 1

    if actual_days_riga != required_days_riga:
        raise ValueError("Riga duration does not match constraint.")
    if actual_days_amsterdam != required_days_amsterdam:
        raise ValueError("Amsterdam duration does not match constraint.")
    if actual_days_mykonos != required_days_mykonos:
        raise ValueError("Mykonos duration does not match constraint.")

    # Check flight connectivity:
    # Flight from Riga to Amsterdam on overlapping day (day2)
    if ("Riga", "Amsterdam") not in direct_flights:
        raise ValueError("Direct flight from Riga to Amsterdam not available.")
    # Flight from Amsterdam to Mykonos on overlapping day (day3)
    if ("Amsterdam", "Mykonos") not in direct_flights:
        raise ValueError("Direct flight from Amsterdam to Mykonos not available.")
    
    # Prepare JSON output: each dictionary contains only day_range and place.
    itinerary.append({
        "day_range": f"{riga_start}-{riga_end}",
        "place": "Riga"
    })
    itinerary.append({
        "day_range": f"{amsterdam_start}-{amsterdam_end}",
        "place": "Amsterdam"
    })
    itinerary.append({
        "day_range": f"{mykonos_start}-{mykonos_end}",
        "place": "Mykonos"
    })

    # Output the itinerary as a JSON-formatted dictionary.
    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()