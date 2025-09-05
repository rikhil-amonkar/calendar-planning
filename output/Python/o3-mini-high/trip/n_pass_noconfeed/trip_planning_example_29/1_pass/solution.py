#!/usr/bin/env python3
import json

def compute_itinerary(total_days, dubrovnik_required, krakow_required, frankfurt_required, wedding_start, wedding_end):
    # We assume the itinerary order is: Dubrovnik -> Frankfurt -> Krakow.
    # According to the rules, if a flight occurs on day X, that day counts for both cities.
    #
    # Let the flight from Dubrovnik to Frankfurt occur on day f1.
    # Then, Dubrovnik days = Day 1 to day f1 (inclusive), which gives f1 days.
    # We need Dubrovnik days to equal dubrovnik_required, so:
    f1 = dubrovnik_required

    # Let the flight from Frankfurt to Krakow occur on day f2.
    # Then, Frankfurt days = Days f1 to f2 (inclusive).
    # The number of days in Frankfurt is then: f2 - f1 + 1.
    # We need that to equal frankfurt_required, so:
    f2 = f1 + frankfurt_required - 1

    # Krakow days = Days f2 to total_days (inclusive).
    # So, the number of Krakow days is: total_days - f2 + 1.
    krakow_days = total_days - f2 + 1

    # Check if the Krakow days match the required constraint.
    if krakow_days != krakow_required:
        return None

    # Additionally, the wedding in Krakow must occur between wedding_start and wedding_end.
    # Since we are in Krakow from day f2 to total_days, we require that f2 <= wedding_start.
    if f2 > wedding_start:
        return None

    # Also verify that total_days is not exceeded.
    if f2 < 1 or f2 > total_days:
        return None

    # The available direct flights are:
    # - Dubrovnik <-> Frankfurt and Frankfurt <-> Krakow.
    # Our itinerary (Dubrovnik -> Frankfurt -> Krakow) respects these direct flights.
    
    itinerary = [
        {"day_range": f"Day 1-{f1}", "place": "Dubrovnik"},
        {"day_range": f"Day {f1}-{f2}", "place": "Frankfurt"},
        {"day_range": f"Day {f2}-{total_days}", "place": "Krakow"}
    ]
    
    return {"itinerary": itinerary}

def main():
    total_days = 10
    # Given constraints:
    required_dubrovnik_days = 7  # Must count to 7 days (includes flight day when departing)
    required_krakow_days = 2      # Must count to 2 days (wedding between day 9 and 10)
    required_frankfurt_days = 3   # Must count to 3 days
    # The wedding in Krakow is scheduled between day 9 and day 10.
    wedding_start = 9
    wedding_end = 10

    result = compute_itinerary(total_days, required_dubrovnik_days, required_krakow_days, required_frankfurt_days, wedding_start, wedding_end)
    if result is None:
        result = {"error": "No valid itinerary meeting constraints."}
    print(json.dumps(result))

if __name__ == "__main__":
    main()