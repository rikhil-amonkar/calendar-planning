#!/usr/bin/env python3
import json

def main():
    # Trip constraints
    total_days = 11
    krakow_required = 5
    paris_required = 2
    seville_required = 6

    # Direct flights available:
    # Krakow <-> Paris and Paris <-> Seville
    direct_flights = {("Krakow", "Paris"), ("Paris", "Krakow"), ("Paris", "Seville"), ("Seville", "Paris")}
    
    # Workshop in Krakow must be attended between day 1 and day 5.
    # To satisfy this, we start in Krakow.
    
    # We use flight days where on the day of flight, you count as being in both cities.
    # Let the flight from Krakow to Paris be taken on the day we complete the required days in Krakow.
    flight_day_from_krakow = krakow_required  # Day 5; Days 1-5 count towards Krakow.
    
    # Similarly, let the flight from Paris to Seville be taken on the day we complete Paris' required days.
    # Since the flight day is counted in both Paris and Seville, the effective days in Paris are:
    # flight_day from Krakow to Paris (which is also the first day in Paris) up to flight_day_from_paris.
    flight_day_from_paris = flight_day_from_krakow + paris_required - 1  # 5 + 2 - 1 = Day 6
    
    # Calculate effective days in Seville.
    # Since the flight day from Paris is counted for Seville,
    # Seville days = total_days - flight_day_from_paris + 1.
    effective_seville_days = total_days - flight_day_from_paris + 1
    if effective_seville_days != seville_required:
        raise ValueError("Cannot satisfy the required number of days for Seville with the given constraints.")
    
    # Build the itinerary.
    # Note: If a flight occurs on day X, that day counts for both departure and arrival cities.
    itinerary = []
    
    # Segment 1: Krakow from Day 1 to flight_day_from_krakow.
    itinerary.append({
        "day_range": f"Day 1-{flight_day_from_krakow}",
        "place": "Krakow"
    })
    # Segment 2: Paris from flight_day_from_krakow to flight_day_from_paris.
    itinerary.append({
        "day_range": f"Day {flight_day_from_krakow}-{flight_day_from_paris}",
        "place": "Paris"
    })
    # Segment 3: Seville from flight_day_from_paris to total_days.
    itinerary.append({
        "day_range": f"Day {flight_day_from_paris}-{total_days}",
        "place": "Seville"
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()