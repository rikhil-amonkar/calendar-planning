import json

def plan_itinerary():
    # Input variables (trip constraints)
    total_days = 10
    city_durations = {
        "Krakow": 2,
        "Dubrovnik": 7,
        "Frankfurt": 3
    }
    # Direct flight pairs (undirected)
    direct_flights = [
        ("Frankfurt", "Krakow"),
        ("Dubrovnik", "Frankfurt"),
    ]
    # Event constraint: must be in Krakow between these days (inclusive)
    event_city = "Krakow"
    event_day_range = (9, 10)

    # Build adjacency for direct flights
    adj = {}
    for a, b in direct_flights:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)

    cities = list(city_durations.keys())
    if len(cities) != 3:
        raise ValueError("This solver expects exactly 3 cities.")

    # Validate that all direct flights are between known cities
    for a in adj:
        for b in adj[a]:
            if a not in cities or b not in cities:
                raise ValueError("Direct flights must be between provided cities.")

    # Determine the linear path order: start -> middle -> end
    # The middle city must be connected to the other two
    degrees = {c: len(adj.get(c, [])) for c in cities}
    middle_candidates = [c for c, d in degrees.items() if d == 2]
    if len(middle_candidates) != 1:
        raise ValueError("Graph must form a path of three cities with a single middle city of degree 2.")
    middle = middle_candidates[0]

    # End city must be the event city and adjacent to middle
    if event_city not in cities:
        raise ValueError("Event city not in provided cities.")
    if event_city not in adj.get(middle, set()):
        raise ValueError("Event city must be an endpoint connected directly to the middle city.")

    # The start city is the other neighbor of the middle
    neighbors = list(adj[middle])
    if len(neighbors) != 2:
        raise ValueError("Middle city must have exactly two neighbors.")
    start = neighbors[0] if neighbors[1] == event_city else neighbors[1]
    end = event_city

    # Durations
    dur_start = city_durations[start]
    dur_middle = city_durations[middle]
    dur_end = city_durations[end]

    # The number of flight days equals sum(durations) - total_days (since flight days are double-counted)
    flights_needed = sum(city_durations.values()) - total_days
    if flights_needed != 2:
        raise ValueError("Constraint mismatch: need exactly two flight days to satisfy durations with overlaps.")

    # Place the end city so that it covers the event days and fits at the end of the trip
    # We will place the end city to end on total_days so that it includes the event window.
    s_end = total_days - dur_end + 1
    e_end = total_days
    # Validate event coverage
    ev_s, ev_e = event_day_range
    if not (s_end <= ev_s and ev_e <= e_end):
        raise ValueError("Cannot place the end city to cover the event days with given durations.")

    # Place the middle city so that it ends on the first day of the end city's range (overlapping on flight day)
    s_middle = s_end - dur_middle + 1
    e_middle = s_end
    if s_middle < 1:
        raise ValueError("Middle city placement exceeds trip start.")

    # Place the start city from day 1 to the first day of the middle city's range (overlapping on flight day)
    s_start = 1
    e_start = s_middle
    # Validate durations align
    if (e_start - s_start + 1) != dur_start:
        raise ValueError("Start city duration mismatch after placement.")
    if (e_middle - s_middle + 1) != dur_middle:
        raise ValueError("Middle city duration mismatch after placement.")
    if (e_end - s_end + 1) != dur_end:
        raise ValueError("End city duration mismatch after placement.")

    # Validate direct flights for transitions
    if middle not in adj.get(start, set()):
        raise ValueError(f"No direct flight between {start} and {middle}.")
    if end not in adj.get(middle, set()):
        raise ValueError(f"No direct flight between {middle} and {end}.")

    # Build itinerary with overlapping day ranges on flight days
    itinerary = [
        {"day_range": f"Day {s_start}-{e_start}", "place": start},
        {"day_range": f"Day {s_middle}-{e_middle}", "place": middle},
        {"day_range": f"Day {s_end}-{e_end}", "place": end},
    ]

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_itinerary()
    print(json.dumps(result))