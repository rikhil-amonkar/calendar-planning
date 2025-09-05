import json
import itertools

def main():
    # Total trip days available
    total_days = 13

    # Required durations for each city
    durations = {
        "Dublin": 3,
        "Madrid": 2,
        "Oslo": 3,
        "London": 2,
        "Vilnius": 3,
        "Berlin": 5
    }

    # Event constraints: each event is defined by an allowed window (inclusive)
    # For a valid stay in that city, its day interval must overlap with the event window.
    events = {
        "Dublin": (7, 9),  # friend meeting in Dublin must be between Day 7 and Day 9
        "Madrid": (2, 3),  # relatives in Madrid must be visited between Day 2 and Day 3
        "Berlin": (3, 7)   # wedding in Berlin must be attended between Day 3 and Day 7
    }

    # Direct flight connections (bidirectional)
    flights = {
        "London": ["Madrid", "Oslo", "Dublin", "Berlin"],
        "Madrid": ["London", "Oslo", "Dublin", "Berlin"],
        "Oslo": ["Vilnius", "Madrid", "London", "Berlin", "Dublin"],
        "Dublin": ["Madrid", "Oslo", "London", "Berlin"],
        "Vilnius": ["Oslo", "Berlin"],
        "Berlin": ["Vilnius", "Madrid", "Oslo", "Dublin", "London"]
    }

    cities = list(durations.keys())

    valid_itinerary = None

    # Iterate over all possible orders (permutations) of the 6 cities
    for perm in itertools.permutations(cities):
        # Check direct flight connectivity for every consecutive pair.
        valid_route = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in flights.get(perm[i], []):
                valid_route = False
                break
        if not valid_route:
            continue

        # Build the timeline schedule.
        # When flying from city A to B on day X, that day is counted for both A and B.
        schedule = []
        start_day = 1
        for city in perm:
            end_day = start_day + durations[city] - 1
            schedule.append((city, start_day, end_day))
            # Next city starts on the same day as the current city's end (overlap)
            start_day = end_day

        # Check if our schedule fits exactly in the total trip days.
        if schedule[-1][2] != total_days:
            continue

        # Check event constraints for cities with specific events.
        meets_events = True
        for city, city_start, city_end in schedule:
            if city in events:
                event_start, event_end = events[city]
                # The city's interval must intersect the event window.
                if city_end < event_start or city_start > event_end:
                    meets_events = False
                    break

        if not meets_events:
            continue

        # Found a valid itinerary.
        valid_itinerary = schedule
        break

    # If no itinerary is found, return an empty itinerary list.
    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        result_list = []
        for city, s_day, e_day in valid_itinerary:
            result_list.append({"day_range": f"Day {s_day}-{e_day}", "place": city})
        result = {"itinerary": result_list}

    print(json.dumps(result))

if __name__ == "__main__":
    main()