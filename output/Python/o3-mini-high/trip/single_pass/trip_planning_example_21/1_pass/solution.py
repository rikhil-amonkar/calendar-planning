#!/usr/bin/env python3
import json

def main():
    # Trip constraints
    total_days = 10
    req_venice = 6       # Must spend 6 days in Venice
    req_mykonos = 2      # Must spend 2 days in Mykonos
    req_vienna = 4       # Must spend 4 days in Vienna
    workshop_start = 5   # Workshop in Venice must be between day 5 and day 10
    workshop_end = 10

    # Allowed direct flights (bidirectional)
    direct_flights = {
        ("Mykonos", "Vienna"), ("Vienna", "Mykonos"),
        ("Vienna", "Venice"),  ("Venice", "Vienna")
    }
    
    # Planned itinerary order based on available flights: Mykonos -> Vienna -> Venice
    cities = ["Mykonos", "Vienna", "Venice"]
    if (cities[0], cities[1]) not in direct_flights or (cities[1], cities[2]) not in direct_flights:
        raise Exception("The required direct flights are not available for the planned cities.")

    # Determine flight days using overlapping rule.
    # If flying from city A to city B on day X, day X counts toward both cities.
    # Let flight_day1 be the day of flight from Mykonos to Vienna.
    # Then Mykonos is visited from Day 1 to flight_day1 (inclusive).
    flight_day1 = req_mykonos  # Must yield exactly req_mykonos days in Mykonos

    # Vienna is visited from flight_day1 to flight_day2 (inclusive),
    # where flight_day2 is the day we fly from Vienna to Venice.
    flight_day2 = flight_day1 + req_vienna - 1  # Overlap of flight day counts for Vienna

    # Venice is visited from flight_day2 to the last day.
    last_day = flight_day2 + req_venice - 1

    # Validate total trip days match
    if last_day != total_days:
        raise Exception("The computed trip duration does not match the total days required.")

    # Validate that Venice visit overlaps with the workshop window
    # Venice visit is from flight_day2 to last_day (inclusive)
    if not (flight_day2 <= workshop_end and last_day >= workshop_start):
        raise Exception("Venice visit does not overlap with the workshop window.")

    # Build the itinerary segments with overlapping flight days.
    itinerary = [
        {"day_range": f"Day 1-{flight_day1}", "place": cities[0]},
        {"day_range": f"Day {flight_day1}-{flight_day2}", "place": cities[1]},
        {"day_range": f"Day {flight_day2}-{last_day}", "place": cities[2]}
    ]

    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()