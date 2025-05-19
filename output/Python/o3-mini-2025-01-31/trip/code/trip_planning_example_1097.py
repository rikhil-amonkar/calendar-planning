#!/usr/bin/env python3
import json

def main():
    # Input trip constraints as provided
    total_days = 18
    # Each city is defined with its required stay duration.
    # Note: Due to overlapping flights, the actual day count is sum(durations) - (number of transitions)
    # There are 8 cities and 7 transitions, so required sum of durations is total_days + 7 = 25 days.
    # The cities and their required durations:
    trip_cities = [
        {"city": "Warsaw",    "stay": 4},  # 4 days
        {"city": "Riga",      "stay": 2},  # 2 days; friend meeting between day 4 and day 5.
        {"city": "Oslo",      "stay": 3},  # 3 days
        {"city": "Dubrovnik", "stay": 2},  # 2 days; wedding between day 7 and day 8.
        {"city": "Madrid",    "stay": 2},  # 2 days
        {"city": "Lyon",      "stay": 5},  # 5 days
        {"city": "London",    "stay": 3},  # 3 days
        {"city": "Reykjavik", "stay": 4}   # 4 days
    ]
    
    # The direct flight connections (used logically to ensure an ordering is possible).
    direct_flights = {
        ("Warsaw", "Reykjavik"),
        ("Oslo", "Madrid"),
        ("Warsaw", "Riga"),
        ("Lyon", "London"),
        ("Madrid", "London"),
        ("Warsaw", "London"),
        ("Reykjavik", "Madrid"),  # Note: given as from Reykjavik to Madrid.
        ("Warsaw", "Oslo"),
        ("Oslo", "Dubrovnik"),
        ("Oslo", "Reykjavik"),
        ("Riga", "Oslo"),
        ("Oslo", "Lyon"),
        ("Oslo", "London"),
        ("London", "Reykjavik"),
        ("Warsaw", "Madrid"),
        ("Madrid", "Lyon"),
        ("Dubrovnik", "Madrid")
    }
    
    # We choose an itinerary order that satisfies:
    # 1. Visiting all 8 cities.
    # 2. Using only cities connected by direct flights.
    # 3. Meeting time constraints:
    #    - Friend in Riga between day 4 and day 5.
    #    - Wedding in Dubrovnik between day 7 and day 8.
    #
    # One valid itinerary:
    # Warsaw -> Riga -> Oslo -> Dubrovnik -> Madrid -> Lyon -> London -> Reykjavik
    #
    # Checks for direct flights along the route:
    # Warsaw -> Riga (exists), Riga -> Oslo (exists), Oslo -> Dubrovnik (exists),
    # Dubrovnik -> Madrid (exists), Madrid -> Lyon (exists),
    # Lyon -> London (exists), London -> Reykjavik (exists).
    
    itinerary_order = ["Warsaw", "Riga", "Oslo", "Dubrovnik", "Madrid", "Lyon", "London", "Reykjavik"]
    
    # Map the stay durations by city name from trip_cities
    stay_durations = {entry["city"]: entry["stay"] for entry in trip_cities}
    
    # Now compute the day ranges.
    # The rule: if you fly from A to B on day X, then on day X you are in both A and B.
    # We assume that the flight occurs at the end of the day of the previous city's stay
    # so that day overlaps.
    itinerary_plan = []
    current_day = 1
    for city in itinerary_order:
        duration = stay_durations[city]
        start_day = current_day
        end_day = start_day + duration - 1
        itinerary_plan.append({"day_range": f"{start_day}-{end_day}", "place": city})
        # For the next city, the flight happens on end_day, so that day is overlapped.
        current_day = end_day

    # Verify that the overall trip duration equals total_days.
    # Sum of stays = 25, overlaps = 7 transitions, 25 - 7 = 18 which equals total_days.
    
    # Output the itinerary as JSON (only including day_range and place).
    print(json.dumps(itinerary_plan, indent=2))

if __name__ == "__main__":
    main()