import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Input variables based on the trip constraints
    total_days = 17
    cities = [
        "Reykjavik", "Stockholm", "Porto", "Nice",
        "Venice", "Vienna", "Split", "Copenhagen"
    ]
    durations = {
        "Reykjavik": 2,
        "Stockholm": 2,
        "Porto": 5,
        "Nice": 3,
        "Venice": 4,
        "Vienna": 3,
        "Split": 3,
        "Copenhagen": 2
    }
    # Direct flights (undirected)
    direct_pairs = [
        ("Copenhagen", "Vienna"),
        ("Nice", "Stockholm"),
        ("Split", "Copenhagen"),
        ("Nice", "Reykjavik"),
        ("Nice", "Porto"),
        ("Reykjavik", "Vienna"),
        ("Stockholm", "Copenhagen"),
        ("Nice", "Venice"),
        ("Nice", "Vienna"),
        ("Reykjavik", "Copenhagen"),
        ("Nice", "Copenhagen"),
        ("Stockholm", "Vienna"),
        ("Venice", "Vienna"),
        ("Copenhagen", "Venice"),
        ("Reykjavik", "Stockholm"),
        ("Stockholm", "Split"),
        ("Split", "Vienna"),
        ("Copenhagen", "Porto"),
        ("Vienna", "Porto"),
    ]
    direct_edges = set(frozenset(p) for p in direct_pairs)

    # Event windows (inclusive day ranges)
    event_windows = {
        "Reykjavik": (3, 4),   # meet friend between day 3 and 4
        "Stockholm": (4, 5),   # meet friends between day 4 and 5
        "Vienna": (11, 13),    # workshop between day 11 and 13
        "Porto": (13, 17),     # wedding between day 13 and 17
    }

    # Problem setup
    problem = Problem()
    pos_vars = [f"pos{i}" for i in range(1, 9)]
    for v in pos_vars:
        problem.addVariable(v, cities)
    problem.addConstraint(AllDifferentConstraint(), pos_vars)

    # Adjacency constraints: consecutive cities must be directly connected
    for i in range(1, 8):
        a, b = f"pos{i}", f"pos{i+1}"
        problem.addConstraint(lambda x, y, E=direct_edges: frozenset((x, y)) in E, (a, b))

    # Global constraint for event windows
    def windows_constraint(*seq):
        seq = list(seq)  # list of city names in order pos1..pos8
        # compute cumulative ends
        ends = []
        e = durations[seq[0]]
        ends.append(e)
        for city in seq[1:]:
            e = e + durations[city] - 1
            ends.append(e)
        # intervals per position
        intervals_by_pos = []
        for i, city in enumerate(seq):
            start = 1 if i == 0 else ends[i-1]
            end = ends[i]
            intervals_by_pos.append((city, (start, end)))

        # map intervals by city
        intervals = {city: rng for city, rng in intervals_by_pos}

        # Check each event window intersects the city's interval
        for city, (w_start, w_end) in event_windows.items():
            c_start, c_end = intervals[city]
            inter_start = max(w_start, c_start)
            inter_end = min(w_end, c_end)
            if inter_start > inter_end:
                return False

        # Implicitly, total ends[-1] should be 17 due to durations sum and overlap day accounting
        return ends[-1] == total_days

    problem.addConstraint(windows_constraint, pos_vars)

    # Solve
    solutions = problem.getSolutions()

    if not solutions:
        print(json.dumps({"itinerary": []}))
        return

    # Scoring: choose itinerary that aligns event city intervals closest to window midpoints
    window_midpoints = {
        "Reykjavik": (event_windows["Reykjavik"][0] + event_windows["Reykjavik"][1]) / 2.0,
        "Stockholm": (event_windows["Stockholm"][0] + event_windows["Stockholm"][1]) / 2.0,
        "Vienna": (event_windows["Vienna"][0] + event_windows["Vienna"][1]) / 2.0,
        "Porto": (event_windows["Porto"][0] + event_windows["Porto"][1]) / 2.0,
    }

    def compute_intervals(seq):
        ends = []
        e = durations[seq[0]]
        ends.append(e)
        for city in seq[1:]:
            e = e + durations[city] - 1
            ends.append(e)
        intervals = {}
        for i, city in enumerate(seq):
            start = 1 if i == 0 else ends[i-1]
            end = ends[i]
            intervals[city] = (start, end)
        return intervals

    def score_solution(seq):
        intervals = compute_intervals(seq)
        score = 0.0
        # Distance from midpoints to nearest presence in city
        for city, mid in window_midpoints.items():
            start, end = intervals[city]
            if mid < start:
                score += (start - mid)
            elif mid > end:
                score += (mid - end)
            else:
                score += 0.0
        return score

    # Select best solution by score, then lexicographic tie-breaker
    best = None
    best_score = None

    for sol in solutions:
        seq = [sol[f"pos{i}"] for i in range(1, 9)]
        sc = score_solution(seq)
        if best is None or sc < best_score or (sc == best_score and tuple(seq) < tuple(best)):
            best = seq
            best_score = sc

    # Build itinerary output
    seq = best
    intervals = compute_intervals(seq)
    # Assemble ordered intervals by sequence position
    ordered_intervals = []
    # Recompute in order of positions
    ends = []
    e = durations[seq[0]]
    ends.append(e)
    ordered_intervals.append((seq[0], (1, e)))
    for i in range(1, len(seq)):
        e = e + durations[seq[i]] - 1
        ordered_intervals.append((seq[i], (ends[i-1], e)))
        ends.append(e)

    itinerary = []
    for city, (start, end) in ordered_intervals:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()