#!/usr/bin/env python3
import json
import sys

# Data: fixed cities with durations (in days)
cities = ["Valencia", "Oslo", "Lyon", "Prague", "Paris", "Nice", "Seville", "Tallinn", "Mykonos", "Lisbon"]
durations = {
    "Valencia": 2,
    "Oslo": 3,
    "Lyon": 4,
    "Prague": 3,
    "Paris": 4,
    "Nice": 4,
    "Seville": 5,
    "Tallinn": 2,
    "Mykonos": 5,
    "Lisbon": 2
}

# Direct flights as an undirected graph.
edges = [
    ("Lisbon", "Paris"),
    ("Lyon", "Nice"),
    ("Tallinn", "Oslo"),
    ("Prague", "Lyon"),
    ("Paris", "Oslo"),
    ("Lisbon", "Seville"),
    ("Prague", "Lisbon"),
    ("Oslo", "Nice"),
    ("Valencia", "Paris"),
    ("Valencia", "Lisbon"),
    ("Paris", "Nice"),
    ("Nice", "Mykonos"),
    ("Paris", "Lyon"),
    ("Valencia", "Lyon"),
    ("Prague", "Oslo"),
    ("Prague", "Paris"),
    ("Seville", "Paris"),
    ("Oslo", "Lyon"),
    ("Prague", "Valencia"),
    ("Lisbon", "Nice"),
    ("Lisbon", "Oslo"),
    ("Valencia", "Seville"),
    ("Lisbon", "Lyon"),
    ("Paris", "Tallinn"),
    ("Prague", "Tallinn")
]

# Build the graph (undirected)
graph = {city: set() for city in cities}
for a, b in edges:
    graph[a].add(b)
    graph[b].add(a)

# Event constraints: Each function takes (start, end) for the city's allocated day range.
# Note: The itinerary is constructed so that if a flight leaves on day X,
# both cities share day X.
event_constraints = {
    # Must meet friends in Valencia between day 3 and day 4.
    "Valencia": lambda s, e: not (e < 3 or s > 4),
    # Annual show in Seville must be attended from day 5 to day 9;
    # with a 5-day stay, the only valid schedule is to have start == 5 (and hence end==9).
    "Seville": lambda s, e: s == 5,
    # Meet a friend in Oslo between day 13 and day 15.
    "Oslo": lambda s, e: not (e < 13 or s > 15),
    # Wedding in Mykonos between day 21 and day 25.
    "Mykonos": lambda s, e: not (e < 21 or s > 25)
}

# Compute the schedule for an ordering.
# The rule: 
# - For the first city, day range is from 1 to durations[city].
# - For each subsequent city, its start day equals the previous city's end day
#   (flight day counts in both cities) and its end day = start + (durations[city]-1).
def compute_schedule(order):
    schedule = []
    if not order:
        return schedule
    # First city
    s = 1
    e = durations[order[0]]
    schedule.append((order[0], s, e))
    # Subsequent cities:
    for city in order[1:]:
        s = schedule[-1][2]  # start equals previous city's end day
        e = s + durations[city] - 1
        schedule.append((city, s, e))
    return schedule

# DFS search to find a valid itinerary order that:
# 1. Uses only allowed direct flights
# 2. Meets event constraints for special cities when they appear.
# 3. Yields a complete itinerary of 25 days.
def dfs(path, remaining):
    if not remaining:
        sched = compute_schedule(path)
        # Final itinerary must end at day 25.
        if sched[-1][2] != 25:
            return None
        # Final check of event constraints.
        for city, s, e in sched:
            if city in event_constraints and not event_constraints[city](s, e):
                return None
        return path

    # For the next candidate city, if path is not empty, enforce direct flight rule.
    last = path[-1] if path else None
    for city in list(remaining):
        # For the very first city, avoid starting with cities that have event constraints
        # that cannot be met if placed first.
        if not path and city in {"Valencia", "Seville", "Oslo", "Mykonos"}:
            continue
        # If not the first city, ensure there's a direct flight from last to current.
        if last is not None and city not in graph[last]:
            continue

        new_path = path + [city]
        sched = compute_schedule(new_path)
        valid = True
        # Check event constraints for the cities already scheduled.
        for (cty, s, e) in sched:
            if cty in event_constraints:
                if not event_constraints[cty](s, e):
                    valid = False
                    break
        # Prune if the partial schedule already exceeds the total 25 days.
        if sched and sched[-1][2] > 25:
            valid = False

        # Also, check if with the remaining cities the total itinerary day count can be met.
        # The full itinerary day count = d(first city) + sum(d(city)-1 for the others).
        # For a partial schedule, the remaining "effective" days if we complete the itinerary is:
        rem_effective = sum(durations[c] - 1 for c in remaining if c != city)
        current = sched[-1][2] if sched else 0
        # The final itinerary day if this branch is completed exactly will be:
        final_day = current + rem_effective
        if final_day > 25:
            valid = False

        if not valid:
            continue

        result = dfs(new_path, remaining - {city})
        if result is not None:
            return result
    return None

def main():
    all_cities = set(cities)
    itinerary_order = dfs([], all_cities)
    if itinerary_order is None:
        print(json.dumps({"itinerary": []}))
        sys.exit(0)
    # Compute full schedule for the found order.
    sched = compute_schedule(itinerary_order)
    # Format the result as a list of dictionaries.
    itinerary_list = []
    for city, s, e in sched:
        itinerary_list.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })
    result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()