import itertools
import json

def can_fly(city1, city2, flight_graph):
    # Check if there's a direct (bidirectional) flight between city1 and city2.
    return city2 in flight_graph.get(city1, []) or city1 in flight_graph.get(city2, [])

def compute_itinerary_segments(order, durations):
    segments = []
    # The rule: the first city starts on day 1 and each flight day is shared.
    # For the first city, days = start_day to (start_day + duration - 1).
    # For each subsequent city, the flight occurs on the same day as the last day of the previous city.
    current_day = 1
    for city in order:
        d = durations[city]
        start_day = current_day
        end_day = start_day + d - 1
        segments.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        # The flight day (end_day) is shared, so it becomes the start day of the next segment.
        current_day = end_day
    return segments

def itinerary_valid(segments, total_days):
    # Check that Stuttgart's segment covers day 7 and day 13.
    for segment in segments:
        if segment["place"] == "Stuttgart":
            # Parse "Day X-Y"
            parts = segment["day_range"].split()[1].split("-")
            start, end = int(parts[0]), int(parts[1])
            if not (start <= 7 <= end and start <= 13 <= end):
                return False
    # Check that Madrid's segment (where relatives are visited) includes a day between 1 and 4.
    for segment in segments:
        if segment["place"] == "Madrid":
            parts = segment["day_range"].split()[1].split("-")
            start, end = int(parts[0]), int(parts[1])
            # There must be an overlap with days 1-4.
            if end < 1 or start > 4:
                return False
    # The final segment must end exactly on total_days.
    last_segment = segments[-1]
    parts = last_segment["day_range"].split()[1].split("-")
    if int(parts[1]) != total_days:
        return False
    return True

def main():
    # Define trip constraints and parameters.
    total_days = 13
    durations = {
        "Madrid": 4,    # Madrid: 4 days (with relatives between day 1 and 4)
        "Seville": 2,   # Seville: 2 days
        "Porto": 3,     # Porto: 3 days
        "Stuttgart": 7  # Stuttgart: 7 days (conference on day 7 and day 13)
    }
    # Direct flights between cities (bidirectional).
    flight_graph = {
        "Madrid": ["Seville", "Porto"],
        "Seville": ["Madrid", "Porto"],
        "Porto": ["Madrid", "Seville", "Stuttgart"],
        "Stuttgart": ["Porto"]
    }

    # The required cities are Madrid, Seville, Porto, and Stuttgart.
    # Because Stuttgart is only directly connected to Porto and because
    # the conference must be attended in Stuttgart on day 7 and day 13,
    # Stuttgart is best placed as the final destination of the itinerary.
    # Further, to fly into Stuttgart from Porto, Porto must immediately precede Stuttgart.
    # Thus, we generate candidate orders for the other three cities,
    # ensuring that the last one is "Porto". Two valid orders emerge:
    #   Option A: ["Madrid", "Seville", "Porto", "Stuttgart"]
    #   Option B: ["Seville", "Madrid", "Porto", "Stuttgart"]
    # We will select the one which puts Madrid as early as possible 
    # so that visiting relatives between day 1 and 4 is ensured.

    candidates = []
    for perm in itertools.permutations(["Madrid", "Seville", "Porto"]):
        if perm[-1] == "Porto":
            order = list(perm) + ["Stuttgart"]
            # Verify connectivity for each consecutive flight.
            valid = True
            for i in range(1, len(order)):
                if not can_fly(order[i-1], order[i], flight_graph):
                    valid = False
                    break
            if valid:
                candidates.append(order)

    # Choose a candidate that satisfies the special constraints.
    selected_order = None
    selected_segments = None
    for order in candidates:
        segments = compute_itinerary_segments(order, durations)
        if itinerary_valid(segments, total_days):
            # Prefer an itinerary starting with Madrid so relatives can be visited from the start.
            if selected_order is None or order[0] == "Madrid":
                selected_order = order
                selected_segments = segments
                break

    # If no valid itinerary is found, return an empty itinerary.
    if selected_segments is None:
        selected_segments = []

    result = {"itinerary": selected_segments}
    print(json.dumps(result))

if __name__ == "__main__":
    main()