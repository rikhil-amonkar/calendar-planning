import itertools
import json

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def is_path_valid(order, adj):
    return all(order[i+1] in adj.get(order[i], set()) for i in range(len(order)-1))

def compute_segments(order, required_days, total_days):
    # Given an order and required per-city days, compute overlapping day ranges per city.
    segments = []
    end = 0
    for idx, city in enumerate(order):
        r = required_days[city]
        if idx == 0:
            start = 1
            end = r
        else:
            start = segments[-1]["end"]  # overlap on boundary day
            end = end + r - 1
        segments.append({"city": city, "start": start, "end": end})
    # Validate total length matches total_days
    if end != total_days:
        return None
    # Validate each segment length equals required days
    for seg in segments:
        if (seg["end"] - seg["start"] + 1) != required_days[seg["city"]]:
            return None
    return segments

def conference_satisfied(segments, conference):
    ccity = conference["city"]
    cstart = conference["start_day"]
    cend = conference["end_day"]
    for seg in segments:
        if seg["city"] == ccity:
            if seg["start"] <= cstart and seg["end"] >= cend:
                return True
    return False

def main():
    # Input variables
    total_days = 14
    cities = ["Vilnius", "Split", "Madrid", "Santorini"]
    required_days = {
        "Vilnius": 4,
        "Split": 5,
        "Madrid": 6,
        "Santorini": 2
    }
    direct_flights = [
        ("Vilnius", "Split"),
        ("Split", "Madrid"),
        ("Madrid", "Santorini")
    ]
    conference = {
        "city": "Santorini",
        "start_day": 13,
        "end_day": 14
    }

    # Pre-computations
    adj = build_adjacency(direct_flights)
    sum_required = sum(required_days[c] for c in cities)
    flights_needed = sum_required - total_days  # due to overlap-on-flight rule

    # We must use exactly (number of cities - 1) flights if we visit each city once
    if flights_needed != len(cities) - 1:
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    valid_itinerary = None

    # Search for a valid permutation that obeys direct-flight constraints and conference days
    for order in itertools.permutations(cities):
        # Must use direct flights along the path
        if not is_path_valid(order, adj):
            continue
        # Compute segments according to order and required days
        segments = compute_segments(order, required_days, total_days)
        if segments is None:
            continue
        # Check conference requirement
        if not conference_satisfied(segments, conference):
            continue
        # Found a valid itinerary
        valid_itinerary = segments
        break

    # Format output
    itinerary_output = []
    if valid_itinerary:
        for seg in valid_itinerary:
            itinerary_output.append({
                "day_range": f"Day {seg['start']}-{seg['end']}",
                "place": seg["city"]
            })

    print(json.dumps({"itinerary": itinerary_output}))

if __name__ == "__main__":
    main()