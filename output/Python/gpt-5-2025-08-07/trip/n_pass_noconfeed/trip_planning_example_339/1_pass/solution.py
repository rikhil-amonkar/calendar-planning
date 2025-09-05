import itertools
import json

def build_adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj

def has_direct_path(seq, adj):
    return all(seq[i+1] in adj.get(seq[i], set()) for i in range(len(seq)-1))

def compute_segments(seq, required_days, total_days):
    # Pre-check: required sum must equal total_days + number_of_flights
    if sum(required_days.values()) != total_days + (len(seq) - 1):
        return None

    end_days = []
    # Compute end days for all but last city
    end_day = 0
    for i, city in enumerate(seq[:-1]):
        if i == 0:
            end_day = required_days[city]
        else:
            end_day = end_day + required_days[city] - 1
        end_days.append(end_day)

    # Build segments as (city, start_day, end_day)
    segments = []
    for i, city in enumerate(seq):
        if i == 0:
            start = 1
            end = end_days[0]
        elif i < len(seq) - 1:
            start = end_days[i-1]
            end = end_days[i]
        else:
            start = end_days[-1]
            end = total_days
        # Validate non-decreasing and ranges
        if end < start or start < 1 or end > total_days:
            return None
        segments.append((city, start, end))

    # Validate durations match requirements
    for city, start, end in segments:
        if (end - start + 1) != required_days[city]:
            return None

    # Validate coverage of all days
    covered = []
    for _, s, e in segments:
        covered.extend(range(s, e + 1))
    if set(covered) != set(range(1, total_days + 1)):
        return None

    # Validate overlaps are only on flight days (shared boundary days)
    # This structure ensures it by construction.

    return segments

def range_intersect_len(a_start, a_end, b_start, b_end):
    lo = max(a_start, b_start)
    hi = min(a_end, b_end)
    return max(0, hi - lo + 1)

def main():
    # Input variables (constraints)
    total_days = 17
    cities = ["Warsaw", "Budapest", "Paris", "Riga"]
    required_days = {
        "Warsaw": 2,
        "Budapest": 7,
        "Paris": 4,
        "Riga": 7
    }
    # Direct flights (undirected)
    direct_edges = [
        ("Warsaw", "Budapest"),
        ("Warsaw", "Riga"),
        ("Budapest", "Paris"),
        ("Warsaw", "Paris"),
        ("Paris", "Riga")
    ]
    # Event windows
    warsaw_show_window = (1, 2)   # Must be in Warsaw on days 1-2
    riga_wedding_window = (11, 17)  # Want to attend wedding in Riga between day 11 and 17

    adj = build_adjacency(direct_edges)

    # Generate candidate sequences: must start in Warsaw (to be there days 1-2)
    start_city = "Warsaw"
    others = [c for c in cities if c != start_city]
    candidates = []
    for perm in itertools.permutations(others, len(others)):
        seq = (start_city,) + perm
        if has_direct_path(seq, adj):
            segments = compute_segments(seq, required_days, total_days)
            if not segments:
                continue

            # Check event constraints
            # Warsaw show: ensure Warsaw segment covers [1,2]
            warsaw_seg = next((seg for seg in segments if seg[0] == "Warsaw"), None)
            if not warsaw_seg:
                continue
            if not (warsaw_seg[1] <= warsaw_show_window[0] and warsaw_seg[2] >= warsaw_show_window[1]):
                continue

            # Riga wedding: maximize overlap with [11,17]
            riga_seg = next((seg for seg in segments if seg[0] == "Riga"), None)
            if not riga_seg:
                continue
            overlap = range_intersect_len(riga_seg[1], riga_seg[2], riga_wedding_window[0], riga_wedding_window[1])
            # Keep any with at least one day overlap; rank by overlap desc
            if overlap >= 1:
                candidates.append((overlap, segments))

    # Choose the candidate with maximum wedding overlap (and stable tie-break by lexicographic city order)
    if not candidates:
        # If none overlap at least one day, still try any valid sequence (fallback)
        for perm in itertools.permutations(others, len(others)):
            seq = (start_city,) + perm
            if has_direct_path(seq, adj):
                segments = compute_segments(seq, required_days, total_days)
                if segments:
                    candidates.append((0, segments))

    if not candidates:
        output = {"itinerary": []}
        print(json.dumps(output, ensure_ascii=False))
        return

    # Sort by overlap desc, then by sequence order for determinism
    candidates.sort(key=lambda x: (-x[0], [seg[0] for seg in x[1]]))
    best_segments = candidates[0][1]

    itinerary = []
    for city, start, end in best_segments:
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()