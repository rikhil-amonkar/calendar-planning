import json
from collections import defaultdict

def build_adjacency(edges):
    adj = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj

def presence_on_day(main_city, day):
    # Presence set on a given day: main_city[day] plus previous day's main if a flight occurred.
    if day == 1:
        return {main_city[1]}
    prev = main_city[day - 1]
    curr = main_city[day]
    if prev != curr:
        return {prev, curr}
    return {curr}

def compute_presence_timeline(main_city, total_days):
    presence_timeline = []
    for d in range(1, total_days + 1):
        presence_timeline.append(presence_on_day(main_city, d))
    return presence_timeline

def count_days_per_city(presence_timeline, cities):
    counts = {c: 0 for c in cities}
    for day_set in presence_timeline:
        for c in day_set:
            counts[c] += 1
    return counts

def check_direct_flights(main_city, adj):
    for d in range(2, len(main_city)):
        a = main_city[d-1]
        b = main_city[d]
        if a != b and b not in adj[a]:
            return False
    return True

def ensure_windows(presence_timeline, must_be_present_days):
    for city, days in must_be_present_days.items():
        for d in days:
            if city not in presence_timeline[d-1]:
                return False
    return True

def at_least_one_in_window(presence_timeline, city, day_range):
    return any(city in presence_timeline[d-1] for d in day_range)

def aggregate_to_ranges(day_places):
    # day_places: list of (day, "place string")
    ranges = []
    if not day_places:
        return ranges
    start_day = day_places[0][0]
    prev_place = day_places[0][1]
    for i in range(1, len(day_places)):
        day, place = day_places[i]
        if place != prev_place:
            # close previous range
            if start_day == day_places[i-1][0]:
                ranges.append({"day_range": f"Day {start_day}", "place": prev_place})
            else:
                ranges.append({"day_range": f"Day {start_day}-{day_places[i-1][0]}", "place": prev_place})
            start_day = day
            prev_place = place
    # close last
    last_day = day_places[-1][0]
    if start_day == last_day:
        ranges.append({"day_range": f"Day {start_day}", "place": prev_place})
    else:
        ranges.append({"day_range": f"Day {start_day}-{last_day}", "place": prev_place})
    return ranges

def main():
    total_days = 20

    # Cities and required exact stay counts (counting flight overlap days as presence in both cities)
    required_days = {
        "Prague": 5,
        "Brussels": 2,
        "Riga": 2,
        "Munich": 2,
        "Seville": 3,
        "Stockholm": 2,
        "Istanbul": 2,
        "Amsterdam": 3,
        "Vienna": 5,
        "Split": 3,
    }
    cities = list(required_days.keys())

    # Direct flight pairs (treated as undirected)
    edges = [
        ("Riga", "Stockholm"),
        ("Stockholm", "Brussels"),
        ("Istanbul", "Munich"),
        ("Istanbul", "Riga"),
        ("Prague", "Split"),
        ("Vienna", "Brussels"),
        ("Vienna", "Riga"),
        ("Split", "Stockholm"),
        ("Munich", "Amsterdam"),
        ("Split", "Amsterdam"),
        ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Riga"),
        ("Vienna", "Stockholm"),
        ("Vienna", "Istanbul"),
        ("Vienna", "Seville"),
        ("Istanbul", "Amsterdam"),
        ("Munich", "Brussels"),
        ("Prague", "Munich"),
        ("Riga", "Munich"),  # "from Riga to Munich" treated as undirected
        ("Prague", "Amsterdam"),
        ("Prague", "Brussels"),
        ("Prague", "Istanbul"),
        ("Istanbul", "Stockholm"),
        ("Vienna", "Prague"),
        ("Munich", "Split"),
        ("Vienna", "Amsterdam"),
        ("Prague", "Stockholm"),
        ("Brussels", "Seville"),
        ("Munich", "Stockholm"),
        ("Istanbul", "Brussels"),
        ("Amsterdam", "Seville"),
        ("Vienna", "Split"),
        ("Munich", "Seville"),
        ("Riga", "Brussels"),
        ("Prague", "Riga"),
        ("Vienna", "Munich"),
    ]
    adj = build_adjacency(edges)

    # Mandatory presence windows (inclusive day indices)
    must_be_present_days = {
        "Prague": list(range(5, 10)),     # Day 5-9
        "Split": list(range(11, 14)),     # Day 11-13
        "Riga": [15, 16],                 # Day 15-16
        "Stockholm": [16, 17],            # Day 16-17
    }
    # Vienna friend window: at least one day of presence in 1..5
    vienna_friend_window = list(range(1, 6))

    # Prepare main city per day (1-indexed for readability)
    main_city = [None] * (total_days + 1)

    # Helper functions to set days
    def set_days(days, city):
        for d in days:
            main_city[d] = city

    # Anchor key blocks based on time windows and logical connectivity
    # - Prague anchored on days 5-8 (we will depart on Day 9 so still present in Prague on Day 9 due to flight rule)
    set_days(range(5, 9), "Prague")  # Day 5-8

    # - Split anchored days 11-12 as main city; Day 13 we'll leave Split but be present due to Day 13 flight from Split
    set_days([11, 12], "Split")

    # - Riga on Day 15 (will be present on Day 16 via Day 16 flight)
    set_days([15], "Riga")

    # - Stockholm main on Day 16 (will count as present also Day 17 due to Day 17 flight)
    set_days([16], "Stockholm")

    # - Vienna: to hit 5 days and friend window, start trip in Vienna (Day 1-4 main as Vienna, Day 5 presence via flight)
    set_days([1, 2, 3, 4], "Vienna")

    # Now, decide bridging days based on adjacency and remaining needs
    # Utility to compute remaining need quickly
    def compute_remaining_need(current_main):
        # Build current presence to date if available
        presence_timeline_partial = compute_presence_timeline(current_main, total_days)
        counts = count_days_per_city(presence_timeline_partial, cities)
        remaining = {c: max(0, required_days[c] - counts[c]) for c in cities}
        return remaining

    # Day 9-10: choose a city that bridges Prague (Day 8) to Split (Day 11)
    # Candidate must be neighbor of both Prague and Split
    bridge_candidates = list(adj["Prague"].intersection(adj["Split"]))
    # Filter out Prague itself to avoid exceeding target
    bridge_candidates = [c for c in bridge_candidates if c != "Prague"]

    # Compute remaining needs before setting Day 9-10
    rem_before_bridge = compute_remaining_need(main_city)
    # Pick candidate with highest remaining need
    bridge_city = max(bridge_candidates, key=lambda c: rem_before_bridge.get(c, 0))
    set_days([9, 10], bridge_city)  # Day 9-10

    # Day 13: pick city that bridges Split (Day 12) to Riga (Day 15) with a sensible stop on Day 14
    # We want Day 13 city that is a neighbor of Split, and Day 14 city that connects Day 13 to Riga.
    # To satisfy Munich's 2 days and Istanbul's 2 days, select Munich on Day 13 and Istanbul on Day 14 if possible.
    day13_options = list(adj["Split"])
    # For Day 14 options from chosen Day 13 must connect to Riga (Day 15 main)
    # We'll prefer Munich on Day 13 if it allows a Day 14 city that connects to Riga and has remaining need.
    def choose_day13_city():
        rem = compute_remaining_need(main_city)
        # Prioritize Munich explicitly to ensure its 2-day requirement can be met
        if "Munich" in day13_options and any(c in adj["Munich"] and "Riga" in adj[c] for c in adj["Munich"]):
            return "Munich"
        # Otherwise choose the option with best remaining need that allows a connector to Riga
        best = None
        best_score = -1
        for c in day13_options:
            # Check if there exists a day14 city connecting to Riga
            connectors = [x for x in adj[c] if "Riga" in adj[x]]
            if not connectors:
                continue
            score = rem.get(c, 0)
            if score > best_score:
                best = c
                best_score = score
        return best

    day13_city = choose_day13_city()
    if not day13_city:
        raise RuntimeError("Failed to choose a valid Day 13 city.")
    set_days([13], day13_city)

    # Day 14: choose a connector city neighbor of Day 13 that also connects to Riga (Day 15)
    day14_candidates = [c for c in adj[day13_city] if "Riga" in adj[c]]
    # Avoid placing Stockholm before Day 16 to not break its exact 2-day window
    avoid = {"Stockholm"}
    rem_now = compute_remaining_need(main_city)
    day14_candidates_scored = [c for c in day14_candidates if c not in avoid]
    if not day14_candidates_scored:
        day14_candidates_scored = day14_candidates  # fallback if nothing else
    day14_city = max(day14_candidates_scored, key=lambda c: rem_now.get(c, 0))
    set_days([14], day14_city)

    # Day 17: choose a neighbor of Stockholm with high remaining need
    d17_candidates = list(adj["Stockholm"])
    rem_now = compute_remaining_need(main_city)
    # Avoid choosing Stockholm itself and avoid cities that would violate other windows
    d17_candidates = [c for c in d17_candidates if c != "Stockholm"]
    day17_city = max(d17_candidates, key=lambda c: rem_now.get(c, 0))
    set_days([17], day17_city)

    # Day 18: choose neighbor of Day 17 city with high remaining need
    d18_candidates = list(adj[day17_city])
    rem_now = compute_remaining_need(main_city)
    day18_city = max(d18_candidates, key=lambda c: rem_now.get(c, 0))
    set_days([18], day18_city)

    # Day 19: if still needs days in Day 18 city, stay; else choose a neighbor that needs days
    rem_now = compute_remaining_need(main_city)
    if rem_now.get(day18_city, 0) > 1:  # stay to fill more if needed
        set_days([19], day18_city)
    else:
        d19_candidates = [c for c in [day18_city] + list(adj[day18_city])]
        day19_city = max(d19_candidates, key=lambda c: rem_now.get(c, 0))
        set_days([19], day19_city)

    # Day 20: choose neighbor of Day 19 city with remaining need
    rem_now = compute_remaining_need(main_city)
    d20_candidates = list(adj[main_city[19]])
    # Also include staying if it helps
    d20_candidates.append(main_city[19])
    day20_city = max(d20_candidates, key=lambda c: rem_now.get(c, 0))
    set_days([20], day20_city)

    # Final pass: ensure all days are set (some days like Day 11-12 Split already set; verify Day 11 is neighbor of Day 10)
    # If any day remained unset, raise error
    for d in range(1, total_days + 1):
        if main_city[d] is None:
            raise RuntimeError(f"Day {d} is unset in main city plan.")

    # Validate adjacency and constraints
    if not check_direct_flights(main_city, adj):
        raise RuntimeError("Itinerary violates direct flight constraints.")

    presence_timeline = compute_presence_timeline(main_city, total_days)
    if not ensure_windows(presence_timeline, must_be_present_days):
        raise RuntimeError("Itinerary violates mandatory presence windows.")

    # Ensure Vienna friend in Day 1-5 window
    if not at_least_one_in_window(presence_timeline, "Vienna", vienna_friend_window):
        raise RuntimeError("Vienna friend meeting window not satisfied.")

    # Ensure exact day counts per city
    counts = count_days_per_city(presence_timeline, cities)
    if any(counts[c] != required_days[c] for c in cities):
        # If counts don't match, we can print debug; but per instructions, we must output valid JSON.
        # To keep robust, if mismatch occurs, raise error.
        msg = {c: {"required": required_days[c], "actual": counts[c]} for c in cities}
        raise RuntimeError(f"Exact duration mismatch: {msg}")

    # Build day-by-day place strings reflecting presence (including flight overlap)
    day_places = []
    for d in range(1, total_days + 1):
        pres = sorted(list(presence_timeline[d - 1]))
        place_str = " & ".join(pres)
        day_places.append((d, place_str))

    # Aggregate consecutive identical place strings into ranges
    itinerary = aggregate_to_ranges(day_places)

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()