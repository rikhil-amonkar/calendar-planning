#!/usr/bin/env python3
import json

def main():
    # Total trip days and required city durations
    total_days = 19
    durations = {
        'Tallinn': 2,     # Must meet friend between Day 1-2
        'Prague': 3,
        'Lisbon': 2,      # Must attend workshop between Day 4-5
        'Copenhagen': 5,
        'Dubrovnik': 5,
        'Stockholm': 4,   # Wedding between Day 13-16 must be in this block
        'Split': 3,
        'Lyon': 2         # Annual show from Day 18-19 must be here
    }
    
    # Define the mandatory event constraints (for reference)
    events = {
        'Tallinn': {'event': 'Meet friend', 'required_days': (1, 2)},
        'Lisbon': {'event': 'Workshop', 'required_days': (4, 5)},
        'Stockholm': {'event': 'Wedding', 'required_days': (13, 16)},
        'Lyon': {'event': 'Annual Show', 'required_days': (18, 19)}
    }
    
    # Chosen itinerary order that satisfies event timing and overall schedule.
    # The overlapping flight days are taken into account:
    # For each flight from city A -> city B on day X, day X counts for both cities.
    # The real total days = sum(durations) - (number of flights) = 26 - 7 = 19
    city_order = [
        'Tallinn',   # Days 1-2; friend meeting between Day 1 and Day 2.
        'Prague',    # Days 2-4.
        'Lisbon',    # Days 4-5; workshop is on day 4 or 5.
        'Copenhagen',# Days 5-9.
        'Dubrovnik', # Days 9-13.
        'Stockholm', # Days 13-16; wedding takes place between Day 13 and Day 16.
        'Split',     # Days 16-18.
        'Lyon'       # Days 18-19; annual show on Day 18-19.
    ]
    
    # Define the cities that have direct flights (bidirectional),
    # represented as frozensets so that order does not matter.
    direct_flights = {
        frozenset(["Dubrovnik", "Stockholm"]),
        frozenset(["Lisbon", "Copenhagen"]),
        frozenset(["Lisbon", "Lyon"]),
        frozenset(["Copenhagen", "Stockholm"]),
        frozenset(["Copenhagen", "Split"]),
        frozenset(["Prague", "Stockholm"]),
        frozenset(["Tallinn", "Stockholm"]),
        frozenset(["Prague", "Lyon"]),
        frozenset(["Lisbon", "Stockholm"]),
        frozenset(["Prague", "Lisbon"]),
        frozenset(["Stockholm", "Split"]),
        frozenset(["Prague", "Copenhagen"]),
        frozenset(["Split", "Lyon"]),
        frozenset(["Copenhagen", "Dubrovnik"]),
        frozenset(["Prague", "Split"]),
        frozenset(["Tallinn", "Copenhagen"]),
        frozenset(["Tallinn", "Prague"])
    }
    
    # Verify that each consecutive pair in the chosen order has a direct flight.
    for i in range(len(city_order) - 1):
        if frozenset([city_order[i], city_order[i+1]]) not in direct_flights:
            raise ValueError(f"No direct flight between {city_order[i]} and {city_order[i+1]}")
    
    # Calculate the itinerary schedule.
    # Since flying from A to B on day X means X counts for both, the start day for
    # the next city equals the end day of the previous city.
    itinerary = []
    current_day = 1
    for city in city_order:
        duration = durations[city]
        start_day = current_day
        end_day = start_day + duration - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        # Overlapping flight day: next city starts on the same day as current end_day.
        current_day = end_day

    # Output the itinerary as a JSON-formatted dictionary
    output = {"itinerary": itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()