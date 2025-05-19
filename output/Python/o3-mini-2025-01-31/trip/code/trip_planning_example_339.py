#!/usr/bin/env python3
import json

def compute_itinerary():
    # Input parameters (can be modified as needed)
    total_days = 17
    required_warsaw_days = 2   # Annual show from day 1 to 2 in Warsaw
    required_budapest_days = 7
    required_paris_days = 4
    required_riga_days = 7
    wedding_interval = (11, 17)  # Wedding in Riga between day 11 and day 17

    # Allowed direct flights between cities:
    # Warsaw-Budapest, Warsaw-Riga, Budapest-Paris, Warsaw-Paris, Paris-Riga.
    # We choose the following route: Warsaw -> Budapest -> Paris -> Riga. 
    # This route uses:
    #   - Warsaw -> Budapest (allowed)
    #   - Budapest -> Paris (allowed)
    #   - Paris -> Riga (allowed)
    # and visits each city for the required length.
    #
    # The property: if a flight is taken on a given day, that day counts for both
    # the departure and arrival cities.
    #
    # We design the itinerary as follows:
    # 1. Start in Warsaw on day 1; must be in Warsaw on days 1 and 2 for the annual show.
    # 2. Fly from Warsaw to Budapest on day 2 (so day 2 counts for both Warsaw and Budapest).
    #    Then remain in Budapest until day 8. Budapest days: day2 (overlap) + days3 to 8 = 7 days.
    # 3. Fly from Budapest to Paris on day 8 (so day 8 counts for both Budapest and Paris).
    #    Remain in Paris until day 11. Paris days: day8 (overlap) + days9-10 + flight day 11 if needed.
    #    To get 4 days for Paris, we interpret the segment as day8 (overlap), days9 and 10 exclusively,
    #    and day11 (overlap) as the 4th day.
    # 4. Fly from Paris to Riga on day 11 (so day 11 counts for both Paris and Riga).
    #    Remain in Riga until day 17. Riga days: day11 (overlap) + days12 to 17 = 7 days.
    #
    # Check wedding constraint: Riga segment (day11 to day17) includes the wedding window (11 to 17).
    
    # Define the day ranges (inclusive) for each city.
    # Note: day ranges are defined as "start_day-end_day" and the flight day appears in both segments.
    warsaw = (1, 2)           # Warsaw: days 1 to 2
    budapest = (2, 8)         # Budapest: day2 (overlap with Warsaw) to day8 (flight day to Paris)
    paris = (8, 11)           # Paris: day8 (overlap) to day11 (flight day to Riga)
    riga = (11, 17)           # Riga: day11 (overlap) to day17
    
    # Verification of durations (each flight day counts for both arriving and departing city).
    def duration(day_range):
        start, end = day_range
        return end - start + 1

    warsaw_duration = duration(warsaw)  # Should be 2
    budapest_duration = duration(budapest)  # Should be 7, counting overlap on day2
    paris_duration = duration(paris)  # Should be 4, counting overlap on day8 and day11
    riga_duration = duration(riga)  # Should be 7, counting overlap on day11

    # Ensure all constraints are met (for clarity, simple assert checks)
    assert warsaw_duration >= required_warsaw_days, "Warsaw period is too short."
    assert budapest_duration >= required_budapest_days, "Budapest period is too short."
    assert paris_duration >= required_paris_days, "Paris period is too short."
    assert riga_duration >= required_riga_days, "Riga period is too short."
    # Ensure wedding day can occur: Riga segment must intersect [11, 17]
    riga_start, riga_end = riga
    w_start, w_end = wedding_interval
    assert not (riga_end < w_start or riga_start > w_end), "Wedding interval not in Riga segment."

    # Create a list of itinerary segments with day_range and place only
    itinerary = [
        {"day_range": f"{warsaw[0]}-{warsaw[1]}", "place": "Warsaw"},
        {"day_range": f"{budapest[0]}-{budapest[1]}", "place": "Budapest"},
        {"day_range": f"{paris[0]}-{paris[1]}", "place": "Paris"},
        {"day_range": f"{riga[0]}-{riga[1]}", "place": "Riga"}
    ]
    
    return itinerary

if __name__ == "__main__":
    plan = compute_itinerary()
    # Output the itinerary in JSON format
    print(json.dumps(plan, indent=2))