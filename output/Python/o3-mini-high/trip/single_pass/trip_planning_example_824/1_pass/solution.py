#!/usr/bin/env python3
import itertools
import json

def main():
    # Trip constraint parameters
    total_days = 22

    # Cities to visit and their required stay durations (in days)
    durations = {
        "Berlin": 5,      # Must attend annual show from Day 1 to 5.
        "Split": 3,
        "Bucharest": 3,   # Must visit relatives between Day 13 and 15.
        "Riga": 5,
        "Lisbon": 3,
        "Tallinn": 4,
        "Lyon": 5        # Wedding in Lyon must be attended between Day 7 and 11.
    }

    # List of cities (7 cities)
    cities = list(durations.keys())
    
    # Define direct flights available.
    # For symmetric flight connections, we add both directions.
    allowed_flights = set()
    def add_bidirectional(a, b):
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    
    # Adding symmetric flights.
    add_bidirectional("Lisbon", "Bucharest")
    add_bidirectional("Berlin", "Lisbon")
    add_bidirectional("Bucharest", "Riga")
    add_bidirectional("Berlin", "Riga")
    add_bidirectional("Split", "Lyon")
    add_bidirectional("Lisbon", "Riga")
    add_bidirectional("Berlin", "Split")
    add_bidirectional("Lyon", "Lisbon")
    add_bidirectional("Berlin", "Tallinn")
    add_bidirectional("Lyon", "Bucharest")
    
    # Adding the directed flight: from Riga to Tallinn (only allowed in this direction)
    allowed_flights.add(("Riga", "Tallinn"))
    
    # By the trip rules, if you fly on a day, that day counts for both cities.
    # Our convention: For the first city, start day is 1 and end day is (1 + duration - 1).
    # For each subsequent city, its start day is the same as the previous city's end day.
    def compute_segments(itinerary):
        segments = []  # Each segment is a tuple (start_day, end_day) for the city.
        current_day = 1
        for city in itinerary:
            start = current_day
            end = start + durations[city] - 1
            segments.append((start, end))
            # Flight is taken on the day of arrival so next start equals the current city's end.
            current_day = end
        return segments

    # Constraint check:
    # - Berlin must be the first city.
    # - For "Lyon": the wedding must be attended between Day 7 and Day 11,
    #   so the Lyon segment (its stay) must cover at least one day in that window.
    #   We require that Lyon's stay overlaps with the window [7,11].
    # - For "Bucharest": the 3-day stay must exactly fall in the window Day 13 to Day 15.
    #   Since the duration is 3 days, the only possibility is a Bucharest segment exactly from 13 to 15.
    def valid_constraints(itinerary, segments):
        # Berlin must be first and its segment must be Day 1 to 5.
        if itinerary[0] != "Berlin":
            return False
        if segments[0] != (1, 5):
            return False

        # Check Lyon wedding attendance constraint: must overlap with [7, 11]
        if "Lyon" in itinerary:
            idx = itinerary.index("Lyon")
            lyon_start, lyon_end = segments[idx]
            # Overlap exists if Lyon's period has at least one day in [7,11].
            if lyon_end < 7 or lyon_start > 11:
                return False

        # Check Bucharest relative visit constraint:
        if "Bucharest" in itinerary:
            idx = itinerary.index("Bucharest")
            buch_start, buch_end = segments[idx]
            # To fully cover a 3-day period within days 13-15, Bucharest must be exactly Day 13 to 15.
            if buch_start != 13 or buch_end != 15:
                return False

        return True
    
    # To obey the flight connectivity, every consecutive pair must have a direct flight.
    def valid_flights(itinerary):
        for i in range(len(itinerary)-1):
            pair = (itinerary[i], itinerary[i+1])
            if pair not in allowed_flights:
                return False
        return True

    # Since the way segments are computed, the overall trip duration is:
    # final_day = 1 + (sum(durations) - number_of_cities)
    # For our 7 cities: 1 + (28 - 7) = 22 which always equals total_days.
    # So we don't need an extra check for overall trip length.

    # Berlin is fixed to be the starting city.
    remaining_cities = [city for city in cities if city != "Berlin"]
    # Additional constraint: Bucharest's 3-day stay must be exactly in the window 13-15.
    # Given the segment computation rules, Bucharest must appear in the itinerary at a position
    # such that its computed start day equals 13. In our system (where overlap days reduce total count),
    # that happens if Bucharest is the 5th city overall.
    # Since Berlin is fixed at index 0, Bucharest must be at index 4 in the full itinerary.
    
    found_itinerary = None
    # Permute the remaining 6 cities in all orders.
    for perm in itertools.permutations(remaining_cities):
        # Check if Bucharest is at position 3 in perm (so overall index 4)
        if perm[3] != "Bucharest":
            continue
        itinerary = ["Berlin"] + list(perm)
        if not valid_flights(itinerary):
            continue
        segments = compute_segments(itinerary)
        if valid_constraints(itinerary, segments):
            # We found a valid itinerary.
            found_itinerary = []
            for city, (start, end) in zip(itinerary, segments):
                found_itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            break

    if found_itinerary is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": found_itinerary}
    
    print(json.dumps(result))

if __name__ == '__main__':
    main()