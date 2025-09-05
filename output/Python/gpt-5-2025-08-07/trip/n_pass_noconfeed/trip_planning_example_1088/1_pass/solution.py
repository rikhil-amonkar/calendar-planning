import json
import itertools

def main():
    # Input variables (trip constraints)
    total_days = 21
    cities = [
        "Reykjavik",
        "Oslo",
        "Stuttgart",
        "Split",
        "Geneva",
        "Porto",
        "Tallinn",
        "Stockholm",
    ]

    durations = {
        "Reykjavik": 2,
        "Oslo": 5,
        "Stuttgart": 5,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3,
        "Tallinn": 5,
        "Stockholm": 3,
    }

    # Special time constraints
    must_be_in_reykjavik_days = {1, 2}  # conference day 1-2
    must_be_in_porto_days = {19, 20, 21}  # workshop day 19-21
    stockholm_friend_window = (2, 4)  # want to meet between day 2 and day 4 inclusive

    # Direct flights (undirected)
    edges = [
        ("Reykjavik", "Stuttgart"),
        ("Reykjavik", "Stockholm"),
        ("Reykjavik", "Tallinn"),
        ("Stockholm", "Oslo"),
        ("Stuttgart", "Porto"),
        ("Oslo", "Split"),
        ("Stockholm", "Stuttgart"),
        ("Reykjavik", "Oslo"),
        ("Oslo", "Geneva"),
        ("Stockholm", "Split"),
        ("Split", "Stuttgart"),
        ("Tallinn", "Oslo"),
        ("Stockholm", "Geneva"),
        ("Oslo", "Porto"),
        ("Geneva", "Porto"),
        ("Geneva", "Split"),
    ]

    graph = {c: set() for c in cities}
    for a, b in edges:
        graph[a].add(b)
        graph[b].add(a)

    # Helper to compute day ranges given an ordered sequence of cities
    def compute_day_ranges(seq):
        # seq is list of 8 cities
        starts = {}
        ends = {}
        current_start = 1
        for i, city in enumerate(seq):
            starts[city] = current_start
            ends[city] = current_start + durations[city] - 1
            # next segment starts with 1-day overlap
            if i < len(seq) - 1:
                current_start = ends[city]
        return starts, ends

    # Check if itinerary meets key constraints
    def valid_adjacency(seq):
        return all(seq[i+1] in graph[seq[i]] for i in range(len(seq)-1))

    def covers_reykjavik_and_porto(seq, starts, ends):
        # Reykjavik must include days 1-2
        if seq[0] != "Reykjavik":
            return False
        if not must_be_in_reykjavik_days.issubset(set(range(starts["Reykjavik"], ends["Reykjavik"] + 1))):
            return False
        # Porto must be last and include days 19-21
        if seq[-1] != "Porto":
            return False
        porto_days = set(range(starts["Porto"], ends["Porto"] + 1))
        if not must_be_in_porto_days.issubset(porto_days):
            return False
        return True

    def total_unique_days(starts, ends):
        # With overlap rule, unique days from start of first to end of last
        start = starts[min(starts, key=starts.get)]
        end = ends[max(ends, key=ends.get)]
        return end - start + 1

    # Score function to encourage meeting friend window in Stockholm
    def stockholm_window_penalty(starts, ends):
        s = starts["Stockholm"]
        e = ends["Stockholm"]
        win_s, win_e = stockholm_friend_window
        # penalty 0 if overlap, else positive = min gap distance
        if not (e < win_s or s > win_e):
            return 0
        if e < win_s:
            return win_s - e
        else:
            return s - win_e

    # Search for best itinerary
    first_city = "Reykjavik"
    last_city = "Porto"
    middle_cities = [c for c in cities if c not in (first_city, last_city)]

    best = None
    best_score = None

    for perm in itertools.permutations(middle_cities):
        seq = [first_city] + list(perm) + [last_city]
        # Check adjacency
        if not valid_adjacency(seq):
            continue

        # Compute day ranges
        starts, ends = compute_day_ranges(seq)

        # Ensure unique days = total_days
        if total_unique_days(starts, ends) != total_days:
            continue

        # Check Reykjavik and Porto constraints
        if not covers_reykjavik_and_porto(seq, starts, ends):
            continue

        # Score based on Stockholm friend window (lower is better)
        score = stockholm_window_penalty(starts, ends)

        # Pick best (minimize score; tie-breaker by earlier Stockholm start)
        if best is None or score < best_score or (score == best_score and starts["Stockholm"] < best[1]["Stockholm"]):
            best = (seq, starts, ends)
            best_score = score

    if best is None:
        # If no plan found (should not happen with given data), output empty itinerary
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    seq, starts, ends = best

    # Build JSON itinerary
    itinerary = []
    for city in seq:
        day_range = f"Day {starts[city]}-{ends[city]}"
        itinerary.append({"day_range": day_range, "place": city})

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()