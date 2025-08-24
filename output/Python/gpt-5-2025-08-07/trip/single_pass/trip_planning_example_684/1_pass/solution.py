import json
from itertools import permutations

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def compute_schedule(order, durations):
    # Overlapping transition rule: next city's start = previous city's end (flight day counts for both)
    schedule = []
    current_start = 1
    for i, city in enumerate(order):
        if i == 0:
            start = 1
        else:
            start = schedule[-1]["end"]  # flight day overlap
        end = start + durations[city] - 1
        schedule.append({"place": city, "start": start, "end": end})
    return schedule

def windows_satisfied(schedule, windows):
    for entry in schedule:
        city = entry["place"]
        if city in windows:
            ws, we = windows[city]
            if not (entry["start"] <= ws and entry["end"] >= we):
                return False
    return True

def adjacency_satisfied(order, adj):
    for i in range(len(order) - 1):
        a, b = order[i], order[i+1]
        if b not in adj.get(a, set()):
            return False
    return True

def find_itinerary(cities, durations, windows, edges, total_days):
    adj = build_adjacency(edges)

    # Try permutations but prune early using adjacency and window checks incrementally
    city_list = list(cities)

    def backtrack(path, schedule):
        if len(path) == len(city_list):
            # Final checks
            if schedule[-1]["end"] != total_days:
                return None
            if not windows_satisfied(schedule, windows):
                return None
            if not adjacency_satisfied(path, adj):
                return None
            return schedule

        for next_city in city_list:
            if next_city in path:
                continue
            # Adjacency prune
            if path:
                if next_city not in adj.get(path[-1], set()):
                    continue

            # Compute start/end for next_city based on current schedule
            if not schedule:
                start = 1
            else:
                start = schedule[-1]["end"]
            end = start + durations[next_city] - 1

            # Early window pruning for the city being placed
            if next_city in windows:
                ws, we = windows[next_city]
                if not (start <= ws and end >= we):
                    continue

            # Build new schedule incrementally
            new_schedule = schedule + [{"place": next_city, "start": start, "end": end}]

            # Additional quick bound check: if last end would exceed total on completion, it's fine because final end is fixed:
            # sum(durations) - (n-1) equals total_days by construction. So no need for further check here.

            result = backtrack(path + [next_city], new_schedule)
            if result is not None:
                return result
        return None

    return backtrack([], [])

def main():
    # Input variables derived from the problem statement
    total_days = 23
    durations = {
        "Amsterdam": 4,
        "Edinburgh": 5,
        "Brussels": 5,
        "Vienna": 5,
        "Berlin": 4,
        "Reykjavik": 5,
    }
    # Windows are inclusive [start, end]
    windows = {
        "Amsterdam": (5, 8),   # visit relatives between day 5 and day 8
        "Reykjavik": (12, 16), # workshop between day 12 and day 16
        "Berlin": (16, 19),    # meet friend between day 16 and day 19
    }
    # Direct flights (undirected)
    edges = [
        ("Edinburgh", "Berlin"),
        ("Amsterdam", "Berlin"),
        ("Edinburgh", "Amsterdam"),
        ("Vienna", "Berlin"),
        ("Berlin", "Brussels"),
        ("Vienna", "Reykjavik"),
        ("Edinburgh", "Brussels"),
        ("Vienna", "Brussels"),
        ("Amsterdam", "Reykjavik"),
        ("Reykjavik", "Brussels"),
        ("Amsterdam", "Vienna"),
        ("Reykjavik", "Berlin"),
    ]

    cities = set(durations.keys())

    # Validate that the total days implied by durations and transitions can match the trip total
    implied_total = sum(durations.values()) - (len(cities) - 1)
    if implied_total != total_days:
        raise ValueError("Given durations and number of transitions cannot yield total_days.")

    schedule = find_itinerary(cities, durations, windows, edges, total_days)
    if schedule is None:
        raise RuntimeError("No valid itinerary found under given constraints.")

    itinerary = []
    for entry in schedule:
        itinerary.append({
            "day_range": f"Day {entry['start']}-{entry['end']}",
            "place": entry["place"]
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()