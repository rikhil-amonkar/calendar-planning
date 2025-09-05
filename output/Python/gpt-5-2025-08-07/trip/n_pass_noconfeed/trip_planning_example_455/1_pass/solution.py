import itertools
import json

def build_adjacency(direct_pairs):
    adj = {}
    for a, b in direct_pairs:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def path_edges_valid(order, adj):
    return all(order[i+1] in adj.get(order[i], set()) for i in range(len(order) - 1))

def build_itinerary(order, durations):
    segments = []
    start = 1
    for city in order:
        d = durations[city]
        end = start + d - 1
        segments.append({"city": city, "start": start, "end": end})
        start = end  # overlap flight day with next city's start
    return segments

def ranges_intersect(a1, a2, b1, b2):
    return not (a2 < b1 or b2 < a1)

def compute_itinerary(cities, durations, direct_pairs, total_days,
                      friend_city, friend_window, wedding_city, wedding_window):
    # Basic validation of total days based on overlaps
    n = len(cities)
    if sum(durations[c] for c in cities) - (n - 1) != total_days:
        raise ValueError("Total days and durations do not match with overlap rule.")
    
    adj = build_adjacency(direct_pairs)

    # We need to meet friend in Riga between day 1 and 2, which implies Riga should be first.
    start_city = friend_city
    remaining = [c for c in cities if c != start_city]

    best = None
    best_metric = None  # minimize earliest possible wedding day in Istanbul

    for perm in itertools.permutations(remaining):
        order = [start_city] + list(perm)
        if not path_edges_valid(order, adj):
            continue
        # Build itinerary with overlap at transition days
        segments = build_itinerary(order, durations)
        last_day = segments[-1]["end"]
        if last_day != total_days:
            continue

        # Check friend window in Riga
        riga_seg = next(seg for seg in segments if seg["city"] == friend_city)
        if not ranges_intersect(riga_seg["start"], riga_seg["end"], friend_window[0], friend_window[1]):
            continue

        # Check wedding window in Istanbul
        ist_seg = next(seg for seg in segments if seg["city"] == wedding_city)
        if not ranges_intersect(ist_seg["start"], ist_seg["end"], wedding_window[0], wedding_window[1]):
            continue

        # Optimization metric: earliest day we can attend the wedding within the window
        wedding_earliest_day = max(ist_seg["start"], wedding_window[0])
        if wedding_earliest_day > wedding_window[1]:
            continue

        metric = (wedding_earliest_day, ist_seg["start"], order)  # tie-break by Istanbul start then order
        if best is None or metric < best_metric:
            best = segments
            best_metric = metric

    if best is None:
        # As a fallback, raise error (should not happen with given constraints)
        raise ValueError("No feasible itinerary found with the given constraints.")

    # Format output
    itinerary_output = []
    for seg in best:
        itinerary_output.append({
            "day_range": f"Day {seg['start']}-{seg['end']}",
            "place": seg["city"]
        })
    return {"itinerary": itinerary_output}

def main():
    # Input variables based on the prompt
    cities = ["Reykjavik", "Riga", "Warsaw", "Istanbul", "Krakow"]
    durations = {
      "Reykjavik": 7,
      "Riga": 2,
      "Warsaw": 3,
      "Istanbul": 6,
      "Krakow": 7
    }
    total_days = 21
    direct_pairs = [
        ("Istanbul", "Krakow"),
        ("Warsaw", "Reykjavik"),
        ("Istanbul", "Warsaw"),
        ("Riga", "Istanbul"),
        ("Krakow", "Warsaw"),
        ("Riga", "Warsaw")
    ]
    friend_city = "Riga"
    friend_window = (1, 2)  # Between day 1 and day 2 inclusive
    wedding_city = "Istanbul"
    wedding_window = (2, 7)  # Between day 2 and day 7 inclusive

    result = compute_itinerary(
        cities=cities,
        durations=durations,
        direct_pairs=direct_pairs,
        total_days=total_days,
        friend_city=friend_city,
        friend_window=friend_window,
        wedding_city=wedding_city,
        wedding_window=wedding_window
    )
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()