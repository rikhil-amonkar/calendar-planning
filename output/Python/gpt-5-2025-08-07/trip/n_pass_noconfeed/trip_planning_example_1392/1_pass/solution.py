import json
from itertools import permutations

def main():
    # Input variables
    total_days = 24
    cities = [
        "Venice", "Nice", "Naples", "Amsterdam", "Barcelona",
        "Valencia", "Stuttgart", "Porto", "Split"
    ]
    durations = {
        "Naples": 3,
        "Valencia": 5,
        "Stuttgart": 2,
        "Split": 5,
        "Venice": 5,
        "Amsterdam": 4,
        "Nice": 2,
        "Barcelona": 2,
        "Porto": 4
    }
    # Constraints
    venice_required_days = {6, 10}  # Must be in Venice on day 6 and day 10
    barcelona_window = {5, 6}       # Must be in Barcelona on day 5 or 6
    naples_meet_window = {18, 19, 20}  # Meet friend in Naples between day 18-20
    nice_meet_window = {23, 24}     # Meet friends in Nice between day 23-24

    # Direct flights (undirected)
    edges = [
        ("Venice", "Nice"),
        ("Naples", "Amsterdam"),
        ("Barcelona", "Nice"),
        ("Amsterdam", "Nice"),
        ("Stuttgart", "Valencia"),
        ("Stuttgart", "Porto"),
        ("Split", "Stuttgart"),
        ("Split", "Naples"),
        ("Valencia", "Amsterdam"),
        ("Barcelona", "Porto"),
        ("Valencia", "Naples"),
        ("Venice", "Amsterdam"),
        ("Barcelona", "Naples"),
        ("Barcelona", "Valencia"),
        ("Split", "Amsterdam"),
        ("Barcelona", "Venice"),
        ("Stuttgart", "Amsterdam"),
        ("Naples", "Nice"),
        ("Venice", "Stuttgart"),
        ("Split", "Barcelona"),
        ("Porto", "Nice"),
        ("Barcelona", "Stuttgart"),
        ("Venice", "Naples"),
        ("Porto", "Amsterdam"),
        ("Porto", "Valencia"),
        ("Stuttgart", "Naples"),
        ("Barcelona", "Amsterdam"),
    ]

    # Build adjacency set
    adj = {c: set() for c in cities}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)

    # Helper to compute start and end day for a city being placed at position k (0-index)
    # given sum of durations before it
    def city_range(sum_before, pos_index, city):
        start = sum_before - pos_index + 1
        end = start + durations[city] - 1
        return start, end

    # Validate constraints for a city with its computed range
    def check_city_constraints(city, start, end):
        rng = set(range(start, end + 1))
        if city == "Venice":
            # Must be exactly include day 6 and 10; with 5-day stay that implies 6-10
            if not (venice_required_days.issubset(rng) and (end - start + 1) == durations["Venice"]):
                return False
            # Also ensure it's exactly from day 6 to 10
            if not (start == 6 and end == 10):
                return False
        if city == "Barcelona":
            if rng.isdisjoint(barcelona_window):
                return False
        if city == "Naples":
            if rng.isdisjoint(naples_meet_window):
                return False
        if city == "Nice":
            if rng.isdisjoint(nice_meet_window):
                return False
        return True

    # Build itinerary list from sequence
    def build_itinerary(seq):
        itinerary = []
        sum_before = 0
        for i, c in enumerate(seq):
            start, end = city_range(sum_before, i, c)
            itinerary.append({"day_range": f"Day {start}-{end}", "place": c})
            sum_before += durations[c]
        return itinerary

    # Scoring function to prefer certain desirable properties among valid solutions
    def score_itinerary(seq):
        # Higher is better
        # Prefer Nice covering both day 23 and 24 (i.e., start 23 for Nice)
        # Prefer Barcelona including day 5
        sum_before = 0
        score = 0
        for i, c in enumerate(seq):
            start, end = city_range(sum_before, i, c)
            if c == "Nice" and start == 23 and end == 24:
                score += 10
            if c == "Barcelona" and start <= 5 <= end:
                score += 3
            sum_before += durations[c]
        return score

    # Backtracking search
    best_seq = None
    best_score = -1

    # Prefer an order that often helps convergence
    preference_order = ["Split", "Valencia", "Barcelona", "Venice", "Stuttgart", "Porto", "Naples", "Amsterdam", "Nice"]

    def backtrack(seq, used, sum_before):
        nonlocal best_seq, best_score
        if len(seq) == len(cities):
            # Verify full adjacency already ensured; verify last day ends at 24
            # Compute last city end day:
            i = len(seq) - 1
            start, end = city_range(sum_before - durations[seq[-1]], i, seq[-1])
            if end != total_days:
                return
            # All constraints already enforced incrementally
            sc = score_itinerary(seq)
            if sc > best_score:
                best_score = sc
                best_seq = list(seq)
            return

        # Generate candidate cities in preference order
        for c in preference_order:
            if c in used:
                continue
            # Adjacency check with previous city
            if seq:
                prev = seq[-1]
                if c not in adj[prev]:
                    continue

            # Compute start/end for c
            start, end = city_range(sum_before, len(seq), c)
            # Prune if out of global bounds too early
            if start < 1 or end > total_days:
                continue

            # Incremental constraints check for key cities
            if c in {"Venice", "Barcelona", "Naples", "Nice"}:
                if not check_city_constraints(c, start, end):
                    continue

            # Additional pruning: If Venice already placed earlier,
            # ensure day 6 and 10 are not assigned to other cities in a way that conflicts.
            # But overlap is allowed; only ensure Venice specifically has 6 and 10, handled above.

            # Continue recursion
            used.add(c)
            seq.append(c)
            backtrack(seq, used, sum_before + durations[c])
            seq.pop()
            used.remove(c)

    # Start search: try all possible starting cities but in preference order
    for start_city in preference_order:
        seq = []
        used = set()
        # Starting city has no adjacency requirement
        s, e = city_range(0, 0, start_city)  # start=1, end=duration
        # Check constraints if it's a key city
        if start_city in {"Venice", "Barcelona", "Naples", "Nice"}:
            if not check_city_constraints(start_city, s, e):
                continue
        used.add(start_city)
        seq.append(start_city)
        backtrack(seq, used, durations[start_city])

    # If no best found, attempt a full permutation fallback (shouldn't be needed)
    if best_seq is None:
        for perm in permutations(cities):
            # Check adjacency
            ok = True
            for i in range(1, len(perm)):
                if perm[i] not in adj[perm[i-1]]:
                    ok = False
                    break
            if not ok:
                continue
            # Check constraints
            sum_before = 0
            constraints_ok = True
            for i, c in enumerate(perm):
                start, end = city_range(sum_before, i, c)
                # Venice, Barcelona, Naples, Nice constraints
                if c in {"Venice", "Barcelona", "Naples", "Nice"}:
                    if not check_city_constraints(c, start, end):
                        constraints_ok = False
                        break
                sum_before += durations[c]
            if not constraints_ok:
                continue
            # Verify end day
            start, end = city_range(sum_before - durations[perm[-1]], len(perm) - 1, perm[-1])
            if end != total_days:
                continue
            best_seq = list(perm)
            break

    if best_seq is None:
        # No solution found (should not happen with given constraints)
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    # Build final itinerary
    itinerary = build_itinerary(best_seq)
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()