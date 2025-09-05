import itertools
import json

def event_constraints(day_ranges):
    # Vienna: must be in Vienna from day 2 to day 3 (i.e. its stay must cover this period)
    if "Vienna" in day_ranges:
        s, e = day_ranges["Vienna"]
        if not (s <= 2 and e >= 3):
            return False
    # Helsinki: must be in Helsinki between day 3 and day 5 (its stay must cover this period)
    if "Helsinki" in day_ranges:
        s, e = day_ranges["Helsinki"]
        if not (s <= 3 and e >= 5):
            return False
    # Tallinn: must be in Tallinn between day 7 and day 11 (its stay must cover this period)
    if "Tallinn" in day_ranges:
        s, e = day_ranges["Tallinn"]
        if not (s <= 7 and e >= 11):
            return False
    return True

def main():
    # Define the cities and required durations (in days)
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    durations = {
        "Dublin": 5,
        "Helsinki": 3,
        "Riga": 3,
        "Reykjavik": 2,
        "Vienna": 2,
        "Tallinn": 5
    }
    total_trip_days = 15

    # Define direct flights.
    # For pairs given as "A and B", we add both directions.
    # For the flight "from Riga to Tallinn", we add only that direction.
    flights = set()
    # Helsinki <-> Riga
    flights.add(("Helsinki", "Riga"))
    flights.add(("Riga", "Helsinki"))
    # Riga -> Tallinn (one directional)
    flights.add(("Riga", "Tallinn"))
    # Vienna <-> Helsinki
    flights.add(("Vienna", "Helsinki"))
    flights.add(("Helsinki", "Vienna"))
    # Riga <-> Dublin
    flights.add(("Riga", "Dublin"))
    flights.add(("Dublin", "Riga"))
    # Vienna <-> Riga
    flights.add(("Vienna", "Riga"))
    flights.add(("Riga", "Vienna"))
    # Reykjavik <-> Vienna
    flights.add(("Reykjavik", "Vienna"))
    flights.add(("Vienna", "Reykjavik"))
    # Helsinki <-> Dublin
    flights.add(("Helsinki", "Dublin"))
    flights.add(("Dublin", "Helsinki"))
    # Tallinn <-> Dublin
    flights.add(("Tallinn", "Dublin"))
    flights.add(("Dublin", "Tallinn"))
    # Reykjavik <-> Helsinki
    flights.add(("Reykjavik", "Helsinki"))
    flights.add(("Helsinki", "Reykjavik"))
    # Reykjavik <-> Dublin
    flights.add(("Reykjavik", "Dublin"))
    flights.add(("Dublin", "Reykjavik"))
    # Helsinki <-> Tallinn
    flights.add(("Helsinki", "Tallinn"))
    flights.add(("Tallinn", "Helsinki"))
    # Vienna <-> Dublin
    flights.add(("Vienna", "Dublin"))
    flights.add(("Dublin", "Vienna"))
    
    valid_itinerary = None

    # Enumerate all permutations of the cities to search for an itinerary that meets all constraints.
    for perm in itertools.permutations(cities):
        day_ranges = {}
        start_day = 1
        overall_end = 0
        # Compute day ranges for each city in this permutation.
        for city in perm:
            end_day = start_day + durations[city] - 1
            day_ranges[city] = (start_day, end_day)
            overall_end = end_day
            # Overlap: if you fly on end_day, you're in both cities that day.
            start_day = end_day  
        # Check if the overall itinerary totals the required trip days.
        if overall_end != total_trip_days:
            continue
        
        # Check that every consecutive flight is available.
        flight_ok = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in flights:
                flight_ok = False
                break
        if not flight_ok:
            continue
        
        # Check the event-specific constraints.
        if not event_constraints(day_ranges):
            continue

        # If all checks pass, we have found a valid itinerary.
        valid_itinerary = (perm, day_ranges)
        break

    # Construct the output JSON.
    if valid_itinerary is None:
        output = {"itinerary": []}
    else:
        order, day_ranges = valid_itinerary
        itinerary_list = []
        for city in order:
            s, e = day_ranges[city]
            itinerary_list.append({"day_range": f"Day {s}-{e}", "place": city})
        output = {"itinerary": itinerary_list}
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()