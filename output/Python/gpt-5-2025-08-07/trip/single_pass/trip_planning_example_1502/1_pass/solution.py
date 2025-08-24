import json
from itertools import permutations

def build_flight_graph(flight_lines):
    graph = {}
    def add_edge(a, b):
        graph.setdefault(a, set()).add(b)
    for line in flight_lines:
        s = line.strip().rstrip('.').rstrip(',')
        if not s:
            continue
        if s.lower().startswith('from '):
            # format: from A to B
            rest = s[5:]
            parts = rest.split(' to ')
            if len(parts) == 2:
                a = parts[0].strip()
                b = parts[1].strip()
                add_edge(a, b)
        elif ' and ' in s:
            a, b = [p.strip() for p in s.split(' and ')]
            add_edge(a, b)
            add_edge(b, a)
    return graph

def is_consecutive(days):
    return all(days[i] + 1 == days[i+1] for i in range(len(days)-1))

def find_sequences_for_gap(prev_city, next_city, delta, candidates, durations, flights):
    # We want sequences where sum(d_i - 1) = delta
    # and edges: prev_city -> first (if prev_city not None), chain connectivity, last -> next_city
    results = []

    # Special case: empty sequence
    if delta == 0:
        ok = True
        if prev_city is not None:
            ok = next_city in flights.get(prev_city, set())
        if ok:
            results.append([])
        # continue to also consider non-empty sequences that also meet delta==0 (very unlikely with d>=1)
        # but keep for completeness

    cand_list = sorted(list(candidates))  # deterministic order

    def backtrack(current_seq, remaining_set, current_diff):
        if current_diff == delta:
            # Validate last -> next_city adjacency
            if current_seq:
                last = current_seq[-1]
                if next_city not in flights.get(last, set()):
                    return
            else:
                # Empty sequence already handled above, but if reached here, validate too
                if prev_city is not None and next_city not in flights.get(prev_city, set()):
                    return
            results.append(list(current_seq))
            return
        if current_diff > delta:
            return
        # simple upper-bound prune: even if we add all remaining cities, can we reach delta?
        max_additional = sum(durations[c]-1 for c in remaining_set)
        if current_diff + max_additional < delta:
            return

        for c in list(remaining_set):
            # adjacency check
            if current_seq:
                if c not in flights.get(current_seq[-1], set()):
                    continue
            else:
                # first in this gap: must connect from prev_city if exists
                if prev_city is not None and c not in flights.get(prev_city, set()):
                    continue
            # choose
            remaining_set.remove(c)
            backtrack(current_seq + [c], remaining_set, current_diff + (durations[c] - 1))
            # un-choose
            remaining_set.add(c)

    backtrack([], set(cand_list), 0)
    return results

def compute_itinerary():
    # Trip parameters
    total_days = 27

    # City durations and event constraints (must cover specified days)
    cities = {
        "Santorini": {"duration": 3},
        "Valencia": {"duration": 4},
        "Madrid": {"duration": 2, "must_days": [6, 7]},
        "Seville": {"duration": 2},
        "Bucharest": {"duration": 3},
        "Vienna": {"duration": 4, "must_days": [3, 4, 5, 6]},
        "Riga": {"duration": 4, "must_days": [20, 21, 22, 23]},
        "Tallinn": {"duration": 5, "must_days": [23, 24, 25, 26, 27]},
        "Krakow": {"duration": 5, "must_days": [11, 12, 13, 14, 15]},
        "Frankfurt": {"duration": 4},
    }

    # Direct flights list
    flight_lines = [
        "Vienna and Bucharest",
        "Santorini and Madrid",
        "Seville and Valencia",
        "Vienna and Seville",
        "Madrid and Valencia",
        "Bucharest and Riga",
        "Valencia and Bucharest",
        "Santorini and Bucharest",
        "Vienna and Valencia",
        "Vienna and Madrid",
        "Valencia and Krakow",
        "Valencia and Frankfurt",
        "Krakow and Frankfurt",
        "from Riga to Tallinn",
        "Vienna and Krakow",
        "Vienna and Frankfurt",
        "Madrid and Seville",
        "Santorini and Vienna",
        "Vienna and Riga",
        "Frankfurt and Tallinn",
        "Frankfurt and Bucharest",
        "Madrid and Bucharest",
        "Frankfurt and Riga",
        "Madrid and Frankfurt",
    ]

    flights = build_flight_graph(flight_lines)

    durations = {c: cities[c]["duration"] for c in cities}

    # Determine anchor cities (those with explicit must_days that are consecutive and equal to duration)
    anchors = []
    for city, info in cities.items():
        if "must_days" in info:
            days = sorted(info["must_days"])
            if not days or not is_consecutive(days):
                raise ValueError(f"Non-consecutive must_days for {city}")
            if len(days) != info["duration"]:
                # For generality, derive start so that must_days fit within duration (not needed here)
                # We'll anchor at earliest possible start that covers must_days
                # start = max(min(days) - (info["duration"] - len(days)), 1)
                # end = start + info["duration"] - 1
                # But this scenario isn't present; raise for safety.
                raise ValueError(f"Duration mismatch for {city}: duration={info['duration']} vs must_days len={len(days)}")
            anchors.append({"city": city, "start": days[0], "end": days[-1]})

    # Sort anchors by start day
    anchors.sort(key=lambda x: x["start"])

    # Validate the last anchor covers trip end (if not, we could add a post-gap)
    if anchors[-1]["end"] != total_days:
        # If last anchor doesn't end at total_days, we'll allow a post-gap later (handled by gaps)
        pass

    # Build gaps list: each gap defined by (prev_city_name or None, prev_end_day, next_city_name, next_start_day)
    gaps = []

    # Pre-gap from day 1 to first anchor start
    first_anchor = anchors[0]
    gaps.append({
        "prev_city": None,
        "prev_end": 1,
        "next_city": first_anchor["city"],
        "next_start": first_anchor["start"]
    })

    # Gaps between anchors
    for i in range(len(anchors) - 1):
        a = anchors[i]
        b = anchors[i + 1]
        gaps.append({
            "prev_city": a["city"],
            "prev_end": a["end"],
            "next_city": b["city"],
            "next_start": b["start"]
        })

    # Post-gap from last anchor end to trip end (if needed)
    last_anchor = anchors[-1]
    if last_anchor["end"] < total_days:
        gaps.append({
            "prev_city": last_anchor["city"],
            "prev_end": last_anchor["end"],
            "next_city": None,
            "next_start": total_days
        })

    # Flexible cities are those without must_days
    anchor_cities = set(a["city"] for a in anchors)
    flexible_cities = set(cities.keys()) - anchor_cities

    # Solve gaps assigning sequences of flexible cities
    gap_sequences = [None] * len(gaps)

    def solve_gap_index(idx, remaining_flex):
        if idx == len(gaps):
            # All gaps assigned; verify all flexible cities used
            return len(remaining_flex) == 0
        g = gaps[idx]
        prev_city = g["prev_city"]
        next_city = g["next_city"]
        delta = g["next_start"] - g["prev_end"] if next_city is not None else total_days - g["prev_end"]
        # Compute all sequences for this gap
        seqs = find_sequences_for_gap(prev_city, next_city, delta, remaining_flex, durations, flights)
        # Try sequences in order that prefer shorter sequences first (heuristic)
        seqs.sort(key=lambda s: (len(s), s))
        for seq in seqs:
            # Use this sequence if all cities available
            if not set(seq).issubset(remaining_flex):
                continue
            # Assign and recurse
            gap_sequences[idx] = seq
            new_remaining = set(remaining_flex) - set(seq)
            if solve_gap_index(idx + 1, new_remaining):
                return True
        return False

    success = solve_gap_index(0, set(flexible_cities))
    if not success:
        return {"error": "No feasible itinerary found under the given constraints."}

    # Build final ordered list: pre-gap seq, anchor, gap, anchor, ...
    ordered_cities = []
    # Pre-gap
    if gap_sequences:
        ordered_cities.extend(gap_sequences[0])
    # Interleave anchors and their following gap sequences
    for i, a in enumerate(anchors):
        ordered_cities.append(a["city"])
        if i < len(anchors) - 1:
            ordered_cities.extend(gap_sequences[i + 1])
    # If post-gap existed (unlikely here), it would be at the end
    if len(gap_sequences) > len(anchors):
        ordered_cities.extend(gap_sequences[-1])

    # Compute day ranges with overlap rule: next.start = prev.end
    itinerary = []
    day_starts = {}
    day_ends = {}

    current_start = 1
    for city in ordered_cities:
        start = current_start
        end = start + durations[city] - 1
        day_starts[city] = start
        day_ends[city] = end
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        current_start = end  # overlap by 1 day per transition

    # Validations
    # 1) Ensure total coverage ends at total_days
    if itinerary[-1]["day_range"].split()[-1].split('-')[-1]:
        last_range = itinerary[-1]["day_range"]
        last_end = int(last_range.split('-')[-1])
        if last_end != total_days:
            return {"error": f"Itinerary does not end on Day {total_days}. Ends on Day {last_end}."}

    # 2) Ensure anchor days align
    for a in anchors:
        if day_starts.get(a["city"], None) != a["start"] or day_ends.get(a["city"], None) != a["end"]:
            return {"error": f"Anchor misalignment for {a['city']}: expected {a['start']}-{a['end']}, got {day_starts.get(a['city'])}-{day_ends.get(a['city'])}."}

    # 3) Ensure direct flights between consecutive cities
    for i in range(len(ordered_cities) - 1):
        c1 = ordered_cities[i]
        c2 = ordered_cities[i + 1]
        if c2 not in flights.get(c1, set()):
            return {"error": f"No direct flight from {c1} to {c2}."}

    # 4) Ensure all cities visited exactly once
    if len(ordered_cities) != len(set(ordered_cities)) or len(ordered_cities) != len(cities):
        return {"error": "City visit count mismatch (duplicate or missing cities)."}

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))