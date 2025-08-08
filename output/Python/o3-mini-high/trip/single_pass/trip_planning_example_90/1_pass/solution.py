#!/usr/bin/env python3
import json

def compute_itinerary():
    # Trip constraints (days are inclusive)
    total_days = 17
    stay_in_Naples = 5
    stay_in_Vienna = 7
    stay_in_Vilnius = 7
    relatives_visit_start = 1
    relatives_visit_end = 5  # Must visit relatives in Naples between day 1 and day 5

    # Allowed direct flights: Naples <-> Vienna, Vienna <-> Vilnius.
    # To satisfy the "visit relatives in Naples" constraint, we must start in Naples.
    # Overlap rule: if a flight occurs on day X, that day counts for both the departure city and the arrival city.
    #
    # We can choose the following itinerary:
    # - Start in Naples on Day 1 and stay for 5 days.
    #   => Naples: Day 1 to Day 5 (meeting the relatives visit requirement).
    #   (Flight from Naples to Vienna on Day 5)
    # - Arrive in Vienna on Day 5 and stay for 7 days.
    #   => Vienna: Day 5 to Day 11.
    #   (Flight from Vienna to Vilnius on Day 11)
    # - Arrive in Vilnius on Day 11 and stay for 7 days.
    #   => Vilnius: Day 11 to Day 17.
    #
    # Total computed days = (5 + 7 + 7) - 2 (overlap on day 5 and day 11) = 17 days.
    
    # Calculate day ranges based on the overlapping flight days
    naples_start = 1
    naples_end = naples_start + stay_in_Naples - 1  # End day for Naples
    
    # Flight from Naples to Vienna happens on naples_end (Day 5).
    vienna_start = naples_end  # Overlap: Day 5 is in both cities
    vienna_end = vienna_start + stay_in_Vienna - 1  # 5 + 7 - 1 = Day 11
    
    # Flight from Vienna to Vilnius happens on vienna_end (Day 11).
    vilnius_start = vienna_end  # Overlap: Day 11 is in both cities
    vilnius_end = vilnius_start + stay_in_Vilnius - 1  # 11 + 7 - 1 = Day 17

    # For validation, the total trip days computed taking overlap into account is:
    # (Days in Naples + Days in Vienna + Days in Vilnius) - (number of flights) = (5+7+7)-2 = 17.
    computed_total_days = (naples_end - naples_start + 1) + (vienna_end - vienna_start + 1) + (vilnius_end - vilnius_start + 1) - 2
    if computed_total_days != total_days:
        raise ValueError("Computed itinerary does not match the total days constraint.")

    itinerary = [
        {"day_range": f"Day {naples_start}-{naples_end}", "place": "Naples"},
        {"day_range": f"Day {vienna_start}-{vienna_end}", "place": "Vienna"},
        {"day_range": f"Day {vilnius_start}-{vilnius_end}", "place": "Vilnius"}
    ]

    # Output the itinerary as a JSON-formatted dictionary.
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    compute_itinerary()