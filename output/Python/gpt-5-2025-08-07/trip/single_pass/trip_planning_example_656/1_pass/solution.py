import itertools
import json

def build_flight_graph():
    graph = {}
    def add_city(c):
        if c not in graph:
            graph[c] = set()
    def add_bidirectional(a, b):
        add_city(a); add_city(b)
        graph[a].add(b)
        graph[b].add(a)
    def add_direct(a, b):
        add_city(a); add_city(b)
        graph[a].add(b)

    # Build graph based on constraints
    add_bidirectional("Bucharest", "Oslo")
    add_bidirectional("Istanbul", "Oslo")
    add_direct("Reykjavik", "Stuttgart")
    add_bidirectional("Bucharest", "Istanbul")
    add_bidirectional("Stuttgart", "Edinburgh")
    add_bidirectional("Istanbul", "Edinburgh")
    add_bidirectional("Oslo", "Reykjavik")
    add_bidirectional("Istanbul", "Stuttgart")
    add_bidirectional("Oslo", "Edinburgh")

    return graph

def compute_schedule(order, durations):
    schedule = []
    start_day = 1
    for i, city in enumerate(order):
        if i == 0:
            s = start_day
        else:
            # Overlap on travel day: share the last day of previous city
            s = schedule[-1][2]  # previous end day is also current start day
        e = s + durations[city] - 1
        schedule.append((city, s, e))
    total_days = schedule[-1][2]
    return schedule, total_days

def is_path_valid(order, flights):
    for a, b in zip(order, order[1:]):
        if b not in flights.get(a, set()):
            return False
    return True

def overlap_len(a_start, a_end, b_start, b_end):
    start = max(a_start, b_start)
    end = min(a_end, b_end)
    return max(0, end - start + 1)

def main():
    # Input variables (constraints)
    cities = ["Reykjavik", "Istanbul", "Edinburgh", "Oslo", "Stuttgart", "Bucharest"]
    durations = {
        "Reykjavik": 5,
        "Istanbul": 4,
        "Edinburgh": 5,
        "Oslo": 2,
        "Stuttgart": 3,
        "Bucharest": 5
    }
    total_days_target = 19

    # Windows for meetings/visits
    ist_window = (5, 8)  # meet friends in Istanbul between days 5-8
    osl_window = (8, 9)  # visit relatives in Oslo between days 8-9

    flights = build_flight_graph()

    best = None  # (score, penalty, order, schedule)
    for order in itertools.permutations(cities):
        if not is_path_valid(order, flights):
            continue

        schedule, total_days = compute_schedule(order, durations)
        if total_days != total_days_target:
            continue

        # Extract city day ranges
        city_ranges = {city: (s, e) for city, s, e in schedule}

        # Must overlap required windows
        ist_s, ist_e = city_ranges["Istanbul"]
        osl_s, osl_e = city_ranges["Oslo"]

        ist_overlap = overlap_len(ist_s, ist_e, ist_window[0], ist_window[1])
        osl_overlap = overlap_len(osl_s, osl_e, osl_window[0], osl_window[1])

        if ist_overlap == 0 or osl_overlap == 0:
            continue

        # Score: maximize overlap (ideally full overlap: 4 for IST, 2 for OSL)
        score = ist_overlap + osl_overlap

        # Penalty: minimize deviation from ideal starts: IST start at 5, OSL start at 8
        penalty = abs(ist_s - 5) + abs(osl_s - 8)

        # Tiebreakers: lexicographic order of itinerary string to keep deterministic
        order_key = " > ".join(order)

        candidate = (score, -penalty, order_key, order, schedule)

        if best is None or candidate > best:
            best = candidate

    if best is None:
        result = {"error": "No valid itinerary found with given constraints."}
    else:
        _, _, _, order, schedule = best
        itinerary = []
        for city, s, e in schedule:
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        result = {"itinerary": itinerary}

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()