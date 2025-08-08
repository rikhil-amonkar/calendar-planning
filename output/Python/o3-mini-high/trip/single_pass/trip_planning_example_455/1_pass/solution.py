#!/usr/bin/env python3
import itertools
import json

def compute_timeline(order, durations):
    timeline = []
    current_day = 1
    for city in order:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        timeline.append((city, start_day, end_day))
        current_day = end_day
    return timeline

def flights_available(order, flights):
    for i in range(len(order) - 1):
        if order[i+1] not in flights.get(order[i], []):
            return False
    return True

def itinerary_valid(timeline, friend_city, wedding_city):
    # Check friend meeting in Riga must occur between day 1 and day 2.
    for city, start, end in timeline:
        if city == friend_city:
            if start > 2:
                return False
    # Check wedding in Istanbul must have at least one day between day 2 and day 7.
    for city, start, end in timeline:
        if city == wedding_city:
            if not (start <= 7 and end >= 2):
                return False
    return True

def main():
    total_trip_days = 21
    durations = {
        "Reykjavik": 7,
        "Riga": 2,
        "Warsaw": 3,
        "Istanbul": 6,
        "Krakow": 7
    }
    # Define bidirectional direct flights.
    flights = {
        "Istanbul": ["Krakow", "Warsaw", "Riga"],
        "Krakow": ["Istanbul", "Warsaw"],
        "Warsaw": ["Reykjavik", "Istanbul", "Krakow", "Riga"],
        "Reykjavik": ["Warsaw"],
        "Riga": ["Istanbul", "Warsaw"]
    }
    friend_city = "Riga"      # Must meet friend in Riga between day 1 and day 2.
    wedding_city = "Istanbul" # Wedding in Istanbul between day 2 and day 7.

    cities = list(durations.keys())
    valid_timeline = None

    # Enforce that the itinerary starts with Riga to satisfy the friend meeting constraint.
    for perm in itertools.permutations(cities):
        if perm[0] != friend_city:
            continue
        if not flights_available(perm, flights):
            continue
        timeline = compute_timeline(perm, durations)
        if timeline[-1][2] != total_trip_days:
            continue
        if not itinerary_valid(timeline, friend_city, wedding_city):
            continue
        valid_timeline = timeline
        break

    itinerary_output = {"itinerary": []}
    if valid_timeline:
        for city, start, end in valid_timeline:
            itinerary_output["itinerary"].append({
                "day_range": f"Day {start}-{end}",
                "place": city
            })

    print(json.dumps(itinerary_output))

if __name__ == "__main__":
    main()