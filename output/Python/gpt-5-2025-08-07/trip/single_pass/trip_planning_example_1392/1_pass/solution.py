import json
from itertools import permutations, product

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def inclusive_len(start, end):
    return end - start + 1

def validate_plan(plan, durations, adj, total_days=24):
    # 1) Check each city appears exactly once
    cities_in_plan = [p["place"] for p in plan]
    if len(cities_in_plan) != len(set(cities_in_plan)):
        return False, "Duplicate cities in plan"

    # 2) Check durations and overlaps
    union_days = set()
    sum_durations = 0
    # Check adjacency and overlaps
    for i, seg in enumerate(plan):
        s, e = seg["start"], seg["end"]
        d = inclusive_len(s, e)
        if d != durations[seg["place"]]:
            return False, f"Duration mismatch for {seg['place']}: got {d}, expected {durations[seg['place']]}"
        sum_durations += d
        union_days.update(range(s, e + 1))
        if i > 0:
            prev = plan[i - 1]
            # Overlap must be exactly at one day: start of current == end of previous
            if s != prev["end"]:
                return False, f"Adjacency day overlap mismatch between {prev['place']} and {seg['place']}: expected start {prev['end']}, got {s}"
            # Check direct flight
            if seg["place"] not in adj.get(prev["place"], set()):
                return False, f"No direct flight between {prev['place']} and {seg['place']}"

    # 3) Check total coverage
    if min(union_days) != 1 or max(union_days) != total_days or len(union_days) != total_days:
        return False, "Coverage of days 1..24 is not complete and continuous"

    # 4) Check flights count logic matches overlaps: for N cities, there are N-1 flights; sum durations = total_days + (N-1)
    N = len(plan)
    if sum_durations != total_days + (N - 1):
        return False, "Sum of durations doesn't match total_days + flights"

    return True, "OK"

def main():
    # Input variables
    cities = ["Venice", "Nice", "Naples", "Amsterdam", "Stuttgart", "Valencia", "Split", "Barcelona", "Porto"]
    durations = {
        "Naples": 3,
        "Valencia": 5,
        "Stuttgart": 2,
        "Split": 5,
        "Venice": 5,
        "Amsterdam": 4,
        "Nice": 2,
        "Barcelona": 2,
        "Porto": 4,
    }
    total_days = 24

    # Day-specific constraints (must be in city on these days)
    # For Naples: meet friend between day 18 and day 20 -> choose endpoints to anchor range exactly (since duration is 3)
    required_days = {
        "Venice": {6, 10},           # Must be in Venice on day 6 and 10
        "Barcelona": {5, 6},         # Must be in Barcelona on day 5 and 6
        "Naples": {18, 20},          # Must cover the window endpoints; with duration 3, this fixes it to 18-20
        "Nice": {23, 24},            # Meet friends between day 23 and 24 -> with duration 2, fix to 23-24
    }

    # Direct flights (undirected)
    flight_pairs = [
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
    adj = build_adjacency(flight_pairs)

    # Compute fixed anchored ranges where the required day span equals duration
    anchors = {}
    for city, req in required_days.items():
        min_day = min(req)
        max_day = max(req)
        if inclusive_len(min_day, max_day) == durations[city]:
            anchors[city] = (min_day, max_day)

    # We expect these anchors to be fixed as per constraints
    # Barcelona: 5-6, Venice: 6-10, Naples: 18-20, Nice: 23-24
    required_anchor_set = {"Barcelona", "Venice", "Naples", "Nice"}
    if set(anchors.keys()) != required_anchor_set:
        raise RuntimeError("Anchors could not be fully determined from constraints.")

    # Sort anchors by start day to define the timeline
    anchor_order = sorted(anchors.items(), key=lambda kv: kv[1][0])  # list of (city, (start, end))
    # This should be [('Barcelona',(5,6)), ('Venice',(6,10)), ('Naples',(18,20)), ('Nice',(23,24))]
    # Validate adjacency between anchors that are consecutive or check there is no gap when no variable cities
    # We'll fill gaps explicitly.

    # Build gaps:
    # gap0: before first anchor (start=1 to first_anchor_start)
    first_anchor_city, (first_anchor_start, first_anchor_end) = anchor_order[0]
    gaps = []
    gaps.append(("GAP0", 1, first_anchor_start, None, first_anchor_city))  # from day 1 to first anchor start

    # Gaps between anchors
    for i in range(len(anchor_order) - 1):
        left_city, (ls, le) = anchor_order[i]
        right_city, (rs, re) = anchor_order[i + 1]
        gaps.append(("GAP", le, rs, left_city, right_city))

    # Remaining cities to place (not in anchors)
    remaining_cities = [c for c in cities if c not in anchors]

    # Solve gaps:
    # GAP0 must be filled by exactly one city covering days start..end
    # Because we must visit each city exactly once and build a linear chain.

    # Helper to build the final plan once we find the sequence in the big gap
    def build_plan(gap0_city, gap2_sequence, gap3_city):
        plan = []
        # Gap0
        s, e = gaps[0][1], gaps[0][2]
        plan.append({"place": gap0_city, "start": s, "end": e})
        # Anchors and other gaps in order:
        # anchor 0
        a0_city, (a0s, a0e) = anchor_order[0]
        plan.append({"place": a0_city, "start": a0s, "end": a0e})
        # anchor 1
        a1_city, (a1s, a1e) = anchor_order[1]
        plan.append({"place": a1_city, "start": a1s, "end": a1e})
        # gap2 sequence (between Venice and Naples)
        current_day = a1e
        for c in gap2_sequence:
            d = durations[c]
            seg_s = current_day
            seg_e = seg_s + d - 1
            plan.append({"place": c, "start": seg_s, "end": seg_e})
            current_day = seg_e
        # anchor 2 (Naples)
        a2_city, (a2s, a2e) = anchor_order[2]
        plan.append({"place": a2_city, "start": a2s, "end": a2e})
        # gap3 city (between Naples and Nice)
        d = durations[gap3_city]
        seg_s = a2e
        seg_e = seg_s + d - 1
        plan.append({"place": gap3_city, "start": seg_s, "end": seg_e})
        # anchor 3 (Nice)
        a3_city, (a3s, a3e) = anchor_order[3]
        plan.append({"place": a3_city, "start": a3s, "end": a3e})
        return plan

    # Determine candidates for GAP0
    gap0_label, gap0_start, gap0_end, _, gap0_to_city = gaps[0]
    gap0_len = inclusive_len(gap0_start, gap0_end)
    gap0_candidates = []
    for c in remaining_cities:
        if durations[c] == gap0_len and gap0_to_city in adj.get(c, set()):
            gap0_candidates.append(c)

    # Determine candidate for GAP3 (between Naples and Nice): must be exactly one city with duration (gap3_len) and proper adjacency
    # Gap3 is the last in gaps list
    gap3_label, gap3_start, gap3_end, gap3_from_city, gap3_to_city = gaps[-1]
    gap3_len = inclusive_len(gap3_start, gap3_end)
    # Note: gap3_start == Naples.end (20), gap3_end == Nice.start (23)
    def gap3_options(available):
        opts = []
        for c in available:
            if durations[c] != gap3_len:
                continue
            if c in adj.get(gap3_from_city, set()) and gap3_to_city in adj.get(c, set()):
                opts.append(c)
        return opts

    # Solve GAP2 (between Venice and Naples) via DFS over the remaining three cities
    # We must use exactly all remaining cities after selecting GAP0 and GAP3.
    def solve_gap2(available, left_anchor_city, start_day, right_anchor_city, end_day):
        k = len(available)
        # quick feasibility check: final end = start + sum(durations) - k must equal end_day
        if (start_day + sum(durations[c] for c in available) - k) != end_day:
            return None  # impossible by duration arithmetic

        best_seq = None

        def dfs(prev_city, current_day, remaining, seq):
            nonlocal best_seq
            if not remaining:
                # Must end exactly at end_day and be connected to right anchor
                if current_day == end_day and right_anchor_city in adj.get(prev_city, set()):
                    best_seq = seq[:]
                return
            # Choose next city
            for c in list(remaining):
                # adjacency from prev_city to c
                if c not in adj.get(prev_city, set()):
                    continue
                # place c starting at current_day
                seg_s = current_day
                seg_e = seg_s + durations[c] - 1
                # No need to check bounds now; the arithmetic feasibility was already checked
                remaining.remove(c)
                seq.append(c)
                dfs(c, seg_e, remaining, seq)
                if best_seq is not None:
                    return
                seq.pop()
                remaining.add(c)

        rem = set(available)
        dfs(left_anchor_city, start_day, rem, [])
        return best_seq

    # Now search for a valid itinerary
    solution_plan = None
    for gap0_city in gap0_candidates:
        rem_after_gap0 = [c for c in remaining_cities if c != gap0_city]
        # Determine GAP3 candidates from the remaining set
        for gap3_city in gap3_options(rem_after_gap0):
            rem_after_gap3 = [c for c in rem_after_gap0 if c != gap3_city]
            # Solve GAP2 using all remaining cities
            # GAP2 is between anchors[1] (Venice) and anchors[2] (Naples)
            left_anchor_city, (left_s, left_e) = anchor_order[1]  # Venice
            right_anchor_city, (right_s, right_e) = anchor_order[2]  # Naples
            gap2_sequence = solve_gap2(
                rem_after_gap3,
                left_anchor_city=left_anchor_city,
                start_day=left_e,
                right_anchor_city=right_anchor_city,
                end_day=right_s
            )
            if gap2_sequence is None:
                continue

            # Build full plan and validate
            plan = build_plan(gap0_city, gap2_sequence, gap3_city)
            ok, msg = validate_plan(plan, durations, adj, total_days)
            if ok:
                solution_plan = plan
                break
        if solution_plan:
            break

    if solution_plan is None:
        raise RuntimeError("No feasible itinerary found with the given constraints.")

    # Prepare output
    itinerary_output = []
    for seg in solution_plan:
        itinerary_output.append({
            "day_range": f"Day {seg['start']}-{seg['end']}",
            "place": seg["place"]
        })

    print(json.dumps({"itinerary": itinerary_output}, ensure_ascii=False))

if __name__ == "__main__":
    main()