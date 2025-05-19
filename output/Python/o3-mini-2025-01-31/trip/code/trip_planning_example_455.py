#!/usr/bin/env python3
import json

def main():
    # Input constraints (in days) for each city and special events:
    # Total duration of trip in days:
    total_trip_days = 21
    
    # City required durations (if arriving on a flight day, that day counts for both cities)
    duration = {
        "Reykjavik": 7,
        "Riga": 2,
        "Warsaw": 3,
        "Istanbul": 6,
        "Krakow": 7
    }
    # Special events constraints (for validation or planning):
    # Friend meeting in Riga must occur between day 1 and day 2.
    # Wedding in Istanbul must occur between day 2 and day 7.
    
    # Direct flight connections among cities (bidirectional)
    flights = {
        ("Istanbul", "Krakow"),
        ("Warsaw", "Reykjavik"),
        ("Istanbul", "Warsaw"),
        ("Riga", "Istanbul"),
        ("Krakow", "Warsaw"),
        ("Riga", "Warsaw")
    }
    # For convenience, add symmetric pairs.
    flights |= {(b, a) for (a, b) in flights}
    
    # We have 5 cities. In order to cover the friend and wedding requirements we choose an itinerary order
    # that starts in Riga (to meet the friend on day 1 or 2)
    # and then visits Istanbul early enough (so wedding happens between day 2 and day 7).
    # Among the cities the only possibility to visit Reykjavik is when connected to Warsaw.
    # Thus a valid order using only direct flights is:
    #  Riga -> Istanbul -> Krakow -> Warsaw -> Reykjavik
    #
    # Flight verification:
    # Riga -> Istanbul: allowed (in flights).
    # Istanbul -> Krakow: allowed.
    # Krakow -> Warsaw: allowed.
    # Warsaw -> Reykjavik: allowed.
    
    itinerary_order = ["Riga", "Istanbul", "Krakow", "Warsaw", "Reykjavik"]
    
    # We now assign day ranges to each city segment.
    # IMPORTANT: if a flight occurs on a given day, that day is included in both the city you are leaving and in the city you are arriving.
    # We will schedule flights on the last day of the required duration for that city.
    # With the ordering chosen, we plan as follows:
    # Let the start day be day 1.
    # The first city "Riga" must be covered for 2 days. We are in Riga for day 1 and day 2.
    # We take the flight from Riga to Istanbul on day 2.
    # Istanbul must be covered for 6 days. Istanbul will include the flight day (day 2) and then days 3 to 7.
    # We then fly from Istanbul to Krakow on day 7.
    # Krakow must be 7 days. Krakow will include day 7 and then days 8 to 13.
    # We fly from Krakow to Warsaw on day 13.
    # Warsaw must be 3 days. Warsaw will include day 13 and then days 14 to 15.
    # We fly from Warsaw to Reykjavik on day 15.
    # Reykjavik must be 7 days. Reykjavik will include day 15 and then days 16 to 21.
    
    # Verify that the final day is 21 which matches the total_trip_days.
    # Calculation:
    # Riga: days 1-2 = 2 days
    # Istanbul: days 2-7 = 6 days
    # Krakow: days 7-13 = 7 days
    # Warsaw: days 13-15 = 3 days
    # Reykjavik: days 15-21 = 7 days
    # Even though some days are double-counted on flight transit days,
    # the overall timeline goes from day 1 to day 21.
    
    segments = []
    current_start = 1
    
    # Riga segment:
    # Assign from day 1 to day 2
    riga_start = current_start
    riga_end = riga_start + duration["Riga"] - 1  # 1 + 2 - 1 = 2
    segments.append({"day_range": f"{riga_start}-{riga_end}", "place": "Riga"})
    
    # Flight from Riga to Istanbul happens on day riga_end.
    # Istanbul segment:
    istanbul_start = riga_end  # overlap on day 2 is in both locations.
    istanbul_end = istanbul_start + duration["Istanbul"] - 1  # 2 + 6 - 1 = 7
    segments.append({"day_range": f"{istanbul_start}-{istanbul_end}", "place": "Istanbul"})
    
    # Flight from Istanbul to Krakow on day istanbul_end.
    krakow_start = istanbul_end  # overlap on day 7.
    krakow_end = krakow_start + duration["Krakow"] - 1  # 7 + 7 - 1 = 13
    segments.append({"day_range": f"{krakow_start}-{krakow_end}", "place": "Krakow"})
    
    # Flight from Krakow to Warsaw on day krakow_end.
    warsaw_start = krakow_end  # overlap on day 13.
    warsaw_end = warsaw_start + duration["Warsaw"] - 1  # 13 + 3 - 1 = 15
    segments.append({"day_range": f"{warsaw_start}-{warsaw_end}", "place": "Warsaw"})
    
    # Flight from Warsaw to Reykjavik on day warsaw_end.
    reykjavik_start = warsaw_end  # overlap on day 15.
    reykjavik_end = reykjavik_start + duration["Reykjavik"] - 1  # 15 + 7 - 1 = 21
    segments.append({"day_range": f"{reykjavik_start}-{reykjavik_end}", "place": "Reykjavik"})
    
    # Final check: The trip ends on day 21.
    if reykjavik_end != total_trip_days:
        raise ValueError("Calculated itinerary does not match the total trip days.")
    
    # The itinerary is built.
    # Output the itinerary as a JSON formatted dictionary (list of segments)
    print(json.dumps(segments, indent=2))

if __name__ == "__main__":
    main()