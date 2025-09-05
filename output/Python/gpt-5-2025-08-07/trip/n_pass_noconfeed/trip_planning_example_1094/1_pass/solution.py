import json
from itertools import combinations, permutations
from collections import defaultdict

def build_graph(routes):
    graph = defaultdict(set)
    for line in routes:
        line = line.strip()
        if not line:
            continue
        if line.lower().startswith("from "):
            # format: from A to B
            rest = line[5:].strip()
            if " to " in rest:
                a, b = [x.strip() for x in rest.split(" to ", 1)]
                graph[a].add(b)
        elif " and " in line:
            a, b = [x.strip() for x in line.split(" and ", 1)]
            graph[a].add(b)
            graph[b].add(a)
        else:
            # ignore malformed
            pass
    return graph

def window_length(win):
    return win[1] - win[0] + 1

def enumerate_sequences_for_gap(available, coverage_need, left_city, right_city, durations, graph):
    # Generate all ordered sequences (permutations of subsets of 'available') that:
    # - sum(durations) - (k-1) == coverage_need
    # - connectivity holds: left->seq[0], seq[i]->seq[i+1], seq[-1]->right
    # Special case: k=0 allowed only if coverage_need == 1 and direct flight left->right exists
    sequences = []
    if coverage_need == 1:
        if right_city in graph[left_city]:
            sequences.append([])  # no intermediate cities
    avail_list = list(available)
    n = len(avail_list)
    for k in range(1, n + 1):
        # Required sum of durations if we place k cities:
        required_sum = coverage_need + (k - 1)
        for subset in combinations(avail_list, k):
            # Quick sum check
            s = sum(durations[c] for c in subset)
            if s != required_sum:
                continue
            for perm in permutations(subset):
                # Connectivity check
                ok = True
                prev = left_city
                for c in perm:
                    if c not in graph[prev]:
                        ok = False
                        break
                    prev = c
                if not ok:
                    continue
                if right_city not in graph[prev]:
                    continue
                sequences.append(list(perm))
    # Deduplicate sequences (in case of duplicates)
    unique = []
    seen = set()
    for seq in sequences:
        key = tuple(seq)
        if key not in seen:
            seen.add(key)
            unique.append(seq)
    return unique

def build_itinerary(anchored_blocks, gap_sequences, durations):
    # anchored_blocks sorted by start day
    # gap_sequences is list of sequences between anchored[i] and anchored[i+1]
    segments = []
    # Add first anchored
    segments.append({
        "city": anchored_blocks[0]["city"],
        "start": anchored_blocks[0]["start"],
        "end": anchored_blocks[0]["end"],
    })
    current_end = anchored_blocks[0]["end"]
    # Iterate gaps and following anchors
    for i, seq in enumerate(gap_sequences):
        # Place sequence cities
        for c in seq:
            start = current_end
            end = start + durations[c] - 1
            segments.append({"city": c, "start": start, "end": end})
            current_end = end
        # Append next anchored
        next_anchor = anchored_blocks[i + 1]
        # Sanity: ensure chain meets
        if current_end != next_anchor["start"]:
            raise ValueError(f"Chain mismatch before {next_anchor['city']}: current_end={current_end}, anchor_start={next_anchor['start']}")
        segments.append({"city": next_anchor["city"], "start": next_anchor["start"], "end": next_anchor["end"]})
        current_end = next_anchor["end"]
    return segments

def verify_itinerary(segments, durations, windows, total_days, graph):
    # Check start and end coverage
    if not segments:
        raise ValueError("Empty itinerary")
    if segments[0]["start"] != 1:
        raise ValueError("Itinerary must start on day 1")
    if segments[-1]["end"] != total_days:
        raise ValueError("Itinerary must end on final day")

    # Check flight connectivity between consecutive cities
    for i in range(len(segments) - 1):
        a = segments[i]["city"]
        b = segments[i + 1]["city"]
        # transition occurs on day segments[i]["end"] == segments[i+1]["start"]
        if segments[i]["end"] != segments[i + 1]["start"]:
            raise ValueError(f"Day overlap missing between {a} and {b}")
        if b not in graph[a]:
            raise ValueError(f"No direct flight from {a} to {b} for transition on day {segments[i]['end']}")

    # Build city day sets
    city_days = defaultdict(set)
    for seg in segments:
        for d in range(seg["start"], seg["end"] + 1):
            city_days[seg["city"]].add(d)

    # Durations check
    for city, req in durations.items():
        if len(city_days[city]) != req:
            raise ValueError(f"City {city} has {len(city_days[city])} days but requires {req}")

    # Windows must be fully covered for their cities
    for city, (ws, we) in windows.items():
        for d in range(ws, we + 1):
            if d not in city_days[city]:
                raise ValueError(f"City {city} must include day {d} per window {ws}-{we}")

    # Every day 1..total_days must be covered by at least one city
    covered = set()
    for days in city_days.values():
        covered |= days
    if covered != set(range(1, total_days + 1)):
        missing = sorted(set(range(1, total_days + 1)) - covered)
        raise ValueError(f"Timeline has uncovered days: {missing}")

def main():
    # INPUT VARIABLES
    total_days = 16
    durations = {
        "Vienna": 4,
        "Barcelona": 2,
        "Edinburgh": 4,
        "Krakow": 3,
        "Riga": 4,
        "Hamburg": 2,
        "Paris": 2,
        "Stockholm": 2,
    }
    windows = {
        # City: (start_day, end_day) that must be covered.
        # These are binding windows (e.g., events) and will be anchored if duration equals window length.
        "Paris": (1, 2),          # Wedding between day 1-2; Paris duration is 2 => anchored exactly 1-2
        "Hamburg": (10, 11),      # Conference day 10-11; Hamburg duration is 2 => anchored exactly 10-11
        "Edinburgh": (12, 15),    # Meet friend between day 12-15; Edinburgh duration is 4 => anchored exactly 12-15
        "Stockholm": (15, 16),    # Visit relatives day 15-16; Stockholm duration is 2 => anchored exactly 15-16
    }
    routes = [
        "Hamburg and Stockholm",
        "Vienna and Stockholm",
        "Paris and Edinburgh",
        "Riga and Barcelona",
        "Paris and Riga",
        "Krakow and Barcelona",
        "Edinburgh and Stockholm",
        "Paris and Krakow",
        "Krakow and Stockholm",
        "Riga and Edinburgh",
        "Barcelona and Stockholm",
        "Paris and Stockholm",
        "Krakow and Edinburgh",
        "Vienna and Hamburg",
        "Paris and Hamburg",
        "Riga and Stockholm",
        "Hamburg and Barcelona",
        "Vienna and Barcelona",
        "Krakow and Vienna",
        "from Riga to Hamburg",
        "Barcelona and Edinburgh",
        "Paris and Barcelona",
        "Hamburg and Edinburgh",
        "Paris and Vienna",
        "Vienna and Riga",
    ]

    # Build graph
    graph = build_graph(routes)

    # Determine anchored blocks (where window length equals required duration)
    anchored_blocks = []
    for city, win in windows.items():
        if durations[city] == window_length(win):
            anchored_blocks.append({"city": city, "start": win[0], "end": win[1]})
        else:
            # In this dataset, all windows match durations, so this branch is not used.
            # If needed, more complex placement within window could be implemented.
            raise ValueError(f"Window for {city} does not match duration; dynamic placement not implemented.")

    # Sort anchored by start day
    anchored_blocks.sort(key=lambda x: x["start"])

    # Compute gaps between anchored blocks
    gaps = []
    for i in range(len(anchored_blocks) - 1):
        left = anchored_blocks[i]
        right = anchored_blocks[i + 1]
        coverage_need = right["start"] - left["end"] + 1
        gaps.append({
            "left_city": left["city"],
            "left_end": left["end"],
            "right_city": right["city"],
            "right_start": right["start"],
            "coverage_need": coverage_need
        })

    # Flexible cities are those not anchored
    anchored_cities = {b["city"] for b in anchored_blocks}
    flexible_cities = set(durations.keys()) - anchored_cities

    # Backtracking search to assign sequences to gaps
    solutions = None

    def backtrack(idx, remaining, chosen):
        nonlocal solutions
        if idx == len(gaps):
            if not remaining:
                solutions = chosen[:]
            return
        gap = gaps[idx]
        candidates = enumerate_sequences_for_gap(
            remaining,
            gap["coverage_need"],
            gap["left_city"],
            gap["right_city"],
            durations,
            graph
        )
        # Try candidates
        for seq in candidates:
            next_remaining = set(remaining) - set(seq)
            # Prune: ensure it's still possible to fit remaining cities into remaining gaps by basic sum check
            # Compute min/max possible coverage across remaining gaps with remaining cities; simple feasibility check
            # For small problem we can skip aggressive pruning.
            chosen.append(seq)
            backtrack(idx + 1, next_remaining, chosen)
            if solutions is not None:
                return
            chosen.pop()

    backtrack(0, flexible_cities, [])

    if solutions is None:
        # No solution found
        output = {"itinerary": []}
        print(json.dumps(output))
        return

    # Build final itinerary segments
    segments = build_itinerary(anchored_blocks, solutions, durations)

    # Verify full constraints
    verify_itinerary(segments, durations, windows, total_days, graph)

    # Format output
    itinerary = []
    for seg in segments:
        itinerary.append({
            "day_range": f"Day {seg['start']}-{seg['end']}",
            "place": seg["city"]
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()