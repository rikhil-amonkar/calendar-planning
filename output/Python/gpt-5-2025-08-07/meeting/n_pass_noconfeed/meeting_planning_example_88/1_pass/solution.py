# SOLUTION:
import json
import heapq

def to_minutes(tstr):
    # tstr format expected: 'H:MM' or 'HH:MM' in 24-hour time
    parts = tstr.strip().split(':')
    h = int(parts[0])
    m = int(parts[1])
    return h * 60 + m

def minutes_to_str(m):
    h = (m // 60) % 24
    mi = m % 60
    return f"{h}:{mi:02d}"

def dijkstra_shortest_time(graph, start, goal):
    # graph: dict node -> list of (neighbor, cost)
    if start == goal:
        return 0
    pq = [(0, start)]
    best = {start: 0}
    while pq:
        cost, node = heapq.heappop(pq)
        if node == goal:
            return cost
        if cost > best.get(node, float('inf')):
            continue
        for nbr, w in graph.get(node, []):
            nc = cost + w
            if nc < best.get(nbr, float('inf')):
                best[nbr] = nc
                heapq.heappush(pq, (nc, nbr))
    return float('inf')

def compute_best_meet_schedule(start_location, start_time_min, friends, edges, min_meet_duration=15):
    # Build directed graph adjacency list from edges
    graph = {}
    for (a, b), w in edges.items():
      graph.setdefault(a, []).append((b, w))

    itinerary = []

    # We aim to maximize number of friends met; for ties, maximize total meeting time.
    feasible_plans = []
    for friend in friends:
        person = friend['name']
        location = friend['location']

        # Compute shortest travel time from start location to friend's location
        travel_time = dijkstra_shortest_time(graph, start_location, location)
        if travel_time == float('inf'):
            continue

        # For each availability window, consider feasible meeting segments
        for (a_start, a_end) in friend['availability']:
            avail_start = to_minutes(a_start)
            avail_end = to_minutes(a_end)

            # Earliest we can arrive if we leave immediately
            earliest_arrival = start_time_min + travel_time

            # Earliest feasible meeting start that respects both arrival and availability
            earliest_meet_start = max(avail_start, earliest_arrival)

            # Latest feasible meeting start that allows at least min_meet_duration
            latest_meet_start = avail_end - min_meet_duration

            if earliest_meet_start > latest_meet_start:
                # Not enough overlap for the minimum duration
                continue

            # Consider various possible start times minute-by-minute and pick the best
            # Scoring: maximize meeting duration within window (end at avail_end)
            best_start = None
            best_duration = -1
            for s in range(earliest_meet_start, latest_meet_start + 1):
                e = avail_end
                duration = e - s
                if duration >= min_meet_duration and duration > best_duration:
                    best_duration = duration
                    best_start = s

            if best_start is not None:
                feasible_plans.append({
                    "person": person,
                    "location": location,
                    "start": best_start,
                    "end": avail_end,
                    "duration": avail_end - best_start
                })

    # Optimization objective: meet as many friends as possible.
    # Since we only have one friend in this scenario, pick the single best plan by duration.
    if feasible_plans:
        # If multiple windows/plans existed, choose the one with longest duration, then earliest start.
        feasible_plans.sort(key=lambda x: (-x["duration"], x["start"]))
        plan = feasible_plans[0]
        itinerary.append({
            "action": "meet",
            "location": plan["location"],
            "person": plan["person"],
            "start_time": minutes_to_str(plan["start"]),
            "end_time": minutes_to_str(plan["end"])
        })

    return {"itinerary": itinerary}

def main():
    # Input variables (as described in the prompt)
    start_location = "Sunset District"
    start_time_str = "9:00"  # 9:00AM in 24-hour format
    start_time_min = to_minutes(start_time_str)

    # Travel times (in minutes) - directed
    edges = {
        ("Sunset District", "Golden Gate Park"): 11,
        ("Golden Gate Park", "Sunset District"): 10
    }

    # Friends and their availabilities
    friends = [
        {
            "name": "Joshua",
            "location": "Golden Gate Park",
            "availability": [("20:45", "21:45")]  # 8:45PM to 9:45PM
        }
    ]

    min_meet_duration = 15  # minutes

    result = compute_best_meet_schedule(
        start_location=start_location,
        start_time_min=start_time_min,
        friends=friends,
        edges=edges,
        min_meet_duration=min_meet_duration
    )

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()