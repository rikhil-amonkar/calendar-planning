#!/usr/bin/env python3
import itertools
import json

def build_flight_graph():
    # Cities: "Bucharest", "Vienna", "Reykjavik", "Manchester", "Riga", "Istanbul", "Florence", "Stuttgart"
    # Initialize empty graph entries for each city.
    cities = ["Bucharest", "Vienna", "Reykjavik", "Manchester", "Riga", "Istanbul", "Florence", "Stuttgart"]
    graph = {city: set() for city in cities}

    # For bidirectional flights, add edges both ways.
    def add_bidirectional(a, b):
        graph[a].add(b)
        graph[b].add(a)

    # Allowed flights (most are bidirectional):
    add_bidirectional("Bucharest", "Vienna")         # Bucharest <-> Vienna
    add_bidirectional("Reykjavik", "Vienna")          # Reykjavik <-> Vienna
    add_bidirectional("Manchester", "Vienna")         # Manchester <-> Vienna
    add_bidirectional("Manchester", "Riga")           # Manchester <-> Riga
    add_bidirectional("Riga", "Vienna")               # Riga <-> Vienna
    add_bidirectional("Istanbul", "Vienna")           # Istanbul <-> Vienna
    add_bidirectional("Vienna", "Florence")           # Vienna <-> Florence
    add_bidirectional("Stuttgart", "Vienna")          # Stuttgart <-> Vienna
    add_bidirectional("Riga", "Bucharest")            # Riga <-> Bucharest
    add_bidirectional("Istanbul", "Riga")             # Istanbul <-> Riga
    add_bidirectional("Stuttgart", "Istanbul")        # Stuttgart <-> Istanbul

    # Directional flight: from Reykjavik to Stuttgart only.
    graph["Reykjavik"].add("Stuttgart")
    # (Do not add reverse edge)

    add_bidirectional("Istanbul", "Bucharest")        # Istanbul <-> Bucharest
    add_bidirectional("Manchester", "Istanbul")       # Manchester <-> Istanbul
    add_bidirectional("Manchester", "Bucharest")      # Manchester <-> Bucharest
    add_bidirectional("Stuttgart", "Manchester")      # Stuttgart <-> Manchester

    return graph

def compute_schedule(itinerary, durations):
    # Compute start and finish days for each city in the itinerary.
    # Rule: The first city starts on day 1.
    # When flying from city A to city B on day X, that day is counted in both A and B.
    # So for index 0: start = 1, finish = 1 + d - 1.
    # For i>=1: start[i] = finish[i-1] and finish[i] = start[i] + durations[city] - 1.
    start_days = []
    finish_days = []
    for idx, city in enumerate(itinerary):
        if idx == 0:
            start_day = 1
        else:
            start_day = finish_days[idx-1]  # flight day overlap
        finish_day = start_day + durations[city] - 1
        start_days.append(start_day)
        finish_days.append(finish_day)
    return start_days, finish_days

def itinerary_valid(itinerary, durations, start_days, finish_days, flight_graph):
    # Constraint 1: Istanbul (2 days, show) must have its block cover day 12 and day 13.
    # For a 2-day stay, the only possibility is that the stay is exactly Day 12-13.
    try:
        ist_index = itinerary.index("Istanbul")
    except ValueError:
        return False
    if start_days[ist_index] != 12:
        return False

    # Constraint 2: Bucharest (4 days, workshop) must have a day between day 16 and day 19.
    try:
        b_index = itinerary.index("Bucharest")
    except ValueError:
        return False
    b_start = start_days[b_index]
    b_finish = finish_days[b_index]
    # The Bucharest block covers days b_start to b_finish (inclusive).
    # It must intersect the interval [16,19].
    if b_start > 19 or (b_start + 3) < 16:
        return False

    # Constraint 3: Check connectivity between consecutive cities.
    for i in range(len(itinerary) - 1):
        curr = itinerary[i]
        nxt = itinerary[i+1]
        # Check if there is a flight from curr to nxt.
        if nxt not in flight_graph[curr]:
            return False

    return True

def main():
    # Define trip constraints.
    # Cities with required durations.
    durations = {
        "Riga": 4,
        "Manchester": 5,
        "Bucharest": 4,
        "Florence": 4,
        "Vienna": 2,
        "Istanbul": 2,
        "Reykjavik": 4,
        "Stuttgart": 5
    }
    cities = list(durations.keys())
    
    flight_graph = build_flight_graph()
    
    valid_itinerary = None
    valid_start = None
    valid_finish = None

    # Search over all permutations.
    for permutation in itertools.permutations(cities):
        # Compute schedule (start and finish days) for this itinerary.
        start_days, finish_days = compute_schedule(permutation, durations)
        # Check if final finish day is 23 (should be always, but we check for sanity)
        if finish_days[-1] != 23:
            continue
        # Check constraints and connectivity.
        if itinerary_valid(permutation, durations, start_days, finish_days, flight_graph):
            valid_itinerary = permutation
            valid_start = start_days
            valid_finish = finish_days
            break

    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        itinerary_plan = []
        for city, start_day, finish_day in zip(valid_itinerary, valid_start, valid_finish):
            day_range = "Day {}-{}".format(start_day, finish_day)
            itinerary_plan.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_plan}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()