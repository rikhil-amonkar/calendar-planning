import itertools
import json

def build_undirected_edges(direct_pairs):
    edges = set()
    for a, b in direct_pairs:
        edges.add((a, b))
        edges.add((b, a))
    return edges

def route_is_valid_with_directs(route, edges):
    return all((route[i], route[i+1]) in edges for i in range(len(route)-1))

def compute_itinerary_for_route(route, city_durations, start_day=1):
    # Build overlapping segments: next segment starts on previous segment's end day
    itinerary = []
    current_start = start_day
    for city in route:
        duration = city_durations[city]
        current_end = current_start + duration - 1
        itinerary.append({
            "city": city,
            "start": current_start,
            "end": current_end
        })
        current_start = current_end  # overlap on travel day
    return itinerary

def calendar_span(itinerary):
    # Unique calendar coverage from Day 1 to last end
    return itinerary[-1]["end"] - itinerary[0]["start"] + 1

def city_days_counted(itinerary):
    # Sum of inclusive lengths (counts travel-day overlaps in both cities)
    return sum(seg["end"] - seg["start"] + 1 for seg in itinerary)

def friend_window_satisfied(itinerary, friend_city, friend_window):
    for seg in itinerary:
        if seg["city"] == friend_city:
            a, b = friend_window
            # Check if [seg.start, seg.end] intersects [a, b]
            if not (seg["end"] < a or seg["start"] > b):
                return True
    return False

def select_best_itinerary(cities, city_durations, total_days, friend_city, friend_window, direct_pairs):
    edges = build_undirected_edges(direct_pairs)
    best = None
    # Evaluate all permutations of the cities
    for route in itertools.permutations(cities, len(cities)):
        if not route_is_valid_with_directs(route, edges):
            continue
        itinerary = compute_itinerary_for_route(route, city_durations, start_day=1)
        cal_span = calendar_span(itinerary)
        friend_ok = friend_window_satisfied(itinerary, friend_city, friend_window)
        # Score: prioritize satisfying friend window and exact calendar span
        span_penalty = abs(cal_span - total_days)
        if friend_ok:
            score = (0, span_penalty)  # first key 0 means friend constraint satisfied
        else:
            score = (1, span_penalty)  # higher priority number if not satisfied

        # Keep the best (lowest score), tie-breaker by earliest presence of friend city
        if best is None or score < best["score"]:
            best = {"score": score, "route": route, "itinerary": itinerary}
        elif score == best["score"]:
            # Tie-breaker: earlier start of friend city
            best_friend_start = next(seg["start"] for seg in best["itinerary"] if seg["city"] == friend_city)
            curr_friend_start = next(seg["start"] for seg in itinerary if seg["city"] == friend_city)
            if curr_friend_start < best_friend_start:
                best = {"score": score, "route": route, "itinerary": itinerary}

    return best["itinerary"] if best else None

def format_itinerary_json(itinerary):
    return {
        "itinerary": [
            {
                "day_range": f"Day {seg['start']}-{seg['end']}",
                "place": seg["city"]
            }
            for seg in itinerary
        ]
    }

def main():
    # Input variables (trip constraints)
    total_days = 15
    city_durations = {
        "Stuttgart": 6,
        "Seville": 7,
        "Manchester": 4
    }
    cities = ["Stuttgart", "Seville", "Manchester"]
    friend_city = "Stuttgart"
    friend_window = (1, 6)  # inclusive day numbers
    # Direct flights (undirected)
    direct_pairs = [
        ("Manchester", "Seville"),
        ("Stuttgart", "Manchester")
    ]

    # Compute optimal itinerary
    itinerary = select_best_itinerary(
        cities=cities,
        city_durations=city_durations,
        total_days=total_days,
        friend_city=friend_city,
        friend_window=friend_window,
        direct_pairs=direct_pairs
    )

    # If for some reason not found, fall back to an empty structure
    if itinerary is None:
        output = {"itinerary": []}
    else:
        output = format_itinerary_json(itinerary)

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()