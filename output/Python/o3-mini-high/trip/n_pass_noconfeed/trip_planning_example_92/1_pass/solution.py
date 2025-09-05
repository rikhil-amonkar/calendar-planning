#!/usr/bin/env python3
import json

def main():
    # Trip constraints
    total_trip_days = 12
    dublin_stay = 2
    riga_stay = 5
    vilnius_stay = 7

    # Direct flight connections available:
    # Dublin <-> Riga and Riga -> Vilnius.
    direct_flights = {
        "Dublin": ["Riga"],
        "Riga": ["Dublin", "Vilnius"],
        "Vilnius": []
    }

    # Calculate flight days based on the rule:
    # If a flight happens on day X it is counted for both the origin and destination.
    # Therefore, if we want to be in Dublin for 2 days, we fly from Dublin to Riga on Day 2.
    flight_day_dublin_to_riga = dublin_stay  # Day 2

    # For Riga, we need a total of 5 days.
    # Since Day 2 is counted (arrival day from Dublin) and the flight out counts as well,
    # flight from Riga to Vilnius must occur on:
    flight_day_riga_to_vilnius = flight_day_dublin_to_riga + riga_stay - 1  # Day 2 + 5 - 1 = Day 6

    # For Vilnius, the participant arrives on the flight day and stays until the end.
    calculated_vilnius_days = total_trip_days - flight_day_riga_to_vilnius + 1  # Days 6 to 12 inclusive
    if calculated_vilnius_days != vilnius_stay:
        result = {"error": "Trip plan not feasible with given constraints."}
        print(json.dumps(result))
        return

    # Build the itinerary based on computed flight days.
    itinerary = []
    # Dublin stay: Day 1 to Day 2 (flight day counted in Dublin)
    dublin_range = f"Day 1-{dublin_stay}"
    itinerary.append({"day_range": dublin_range, "place": "Dublin"})

    # Riga stay: from flight day from Dublin (Day 2) to flight day to Vilnius (Day 6)
    riga_range = f"Day {flight_day_dublin_to_riga}-{flight_day_riga_to_vilnius}"
    itinerary.append({"day_range": riga_range, "place": "Riga"})

    # Vilnius stay: from flight day from Riga (Day 6) to the end of the trip (Day 12)
    vilnius_range = f"Day {flight_day_riga_to_vilnius}-{total_trip_days}"
    itinerary.append({"day_range": vilnius_range, "place": "Vilnius"})

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()