import json
from itertools import permutations

def build_graph():
    adj = {}
    def add_bidirectional(a,b):
        adj.setdefault(a,set()).add(b)
        adj.setdefault(b,set()).add(a)
    def add_directed(a,b):
        adj.setdefault(a,set()).add(b)

    # Define direct flights (bidirectional unless specified)
    add_bidirectional("Lisbon","Bucharest")
    add_bidirectional("Berlin","Lisbon")
    add_bidirectional("Bucharest","Riga")
    add_bidirectional("Berlin","Riga")
    add_bidirectional("Split","Lyon")
    add_bidirectional("Lisbon","Riga")
    add_directed("Riga","Tallinn")  # directed
    add_bidirectional("Berlin","Split")
    add_bidirectional("Lyon","Lisbon")
    add_bidirectional("Berlin","Tallinn")
    add_bidirectional("Lyon","Bucharest")
    return adj

def edge_exists(graph, a, b):
    return b in graph.get(a, set())

def find_itinerary():
    trip_days = 22

    # City durations
    durations = {
        "Berlin": 5,
        "Split": 3,
        "Bucharest": 3,
        "Riga": 5,
        "Lisbon": 3,
        "Tallinn": 4,
        "Lyon": 5
    }

    # Fixed windows (inclusive)
    # Must be present in the city for all days in window
    fixed_windows = {
        "Berlin": (1, 5),       # Annual show days 1-5
        "Lyon": (7, 11),        # Wedding days 7-11
        "Bucharest": (13, 15)   # Relatives visit days 13-15
    }

    graph = build_graph()

    # Build anchored segments for fixed windows
    anchors = []
    for city, (ws, we) in fixed_windows.items():
        length = we - ws + 1
        if durations[city] != length:
            # If duration doesn't match window length, no solution under single contiguous-stay model
            return None
        anchors.append((city, ws, we))
    anchors.sort(key=lambda x: x[1])  # sort by start day

    # Ensure first anchor starts at day 1
    if anchors[0][1] != 1:
        return None
    # Ensure we don't violate chronological order
    for i in range(len(anchors)-1):
        if anchors[i][2] > anchors[i+1][1]:
            # Overlapping anchors in a way that breaks single chain logic
            return None

    all_cities = set(durations.keys())
    used_cities = set(city for city,_,_ in anchors)
    remaining_cities = list(all_cities - used_cities)

    # Backtracking to fill gaps between anchors with cities that fit exactly
    sequence = []  # list of (city, start, end) in chronological order

    def try_fill_gaps(anchor_idx, built_sequence, unused_cities):
        if anchor_idx == 0:
            built_sequence.append(anchors[0])
        if anchor_idx == len(anchors) - 1:
            # After placing last anchor, proceed to fill the tail
            return fill_tail(built_sequence, unused_cities)
        # Gap between anchors[anchor_idx] and anchors[anchor_idx+1]
        prev_city, prev_s, prev_e = anchors[anchor_idx]
        next_city, next_s, next_e = anchors[anchor_idx+1]
        gap_len = next_s - prev_e + 1
        # Candidates: durations match gap_len and flights prev->candidate and candidate->next
        candidates = []
        for c in unused_cities:
            if durations[c] == gap_len and edge_exists(graph, prev_city, c) and edge_exists(graph, c, next_city):
                candidates.append(c)

        # Try candidates one by one (backtracking)
        for c in candidates:
            seg = (c, prev_e, next_s)  # start at prev end (overlap), end at next start (overlap)
            new_seq = built_sequence + [seg, anchors[anchor_idx+1]]
            new_unused = [x for x in unused_cities if x != c]
            res = try_fill_gaps(anchor_idx+1, new_seq, new_unused)
            if res is not None:
                return res
        return None

    # Fill remaining days after last anchor
    def fill_tail(built_sequence, unused_cities):
        last_city, last_s, last_e = built_sequence[-1]
        tail_union_len = trip_days - last_e + 1
        # We need an ordered chain of remaining cities whose union with 1-day overlaps equals tail_union_len.
        # With chain start at last_e, next starts overlap exactly previous end.
        for order in permutations(unused_cities):
            # Check flight edges chain
            ok_edges = True
            prev = last_city
            for c in order:
                if not edge_exists(graph, prev, c):
                    ok_edges = False
                    break
                prev = c
            if not ok_edges:
                continue

            # Lay out the days
            cur_start = last_e
            segments = []
            for c in order:
                seg_end = cur_start + durations[c] - 1
                segments.append((c, cur_start, seg_end))
                cur_start = seg_end  # next starts on this same day (overlap)
            if segments:
                final_end = segments[-1][2]
            else:
                final_end = last_e

            # The final day must end exactly on trip_days
            if final_end == trip_days:
                return built_sequence + segments
        return None

    itinerary_segments = try_fill_gaps(0, [], remaining_cities)
    if itinerary_segments is None:
        return None

    # Sanity checks
    itinerary_segments_sorted = sorted(itinerary_segments, key=lambda x: x[1])
    # Check union coverage from day 1 to trip_days without gaps
    covered_start = itinerary_segments_sorted[0][1]
    covered_end = itinerary_segments_sorted[0][2]
    if covered_start != 1:
        return None
    for i in range(1, len(itinerary_segments_sorted)):
        s = itinerary_segments_sorted[i][1]
        e = itinerary_segments_sorted[i][2]
        # Must start on or before previous end to overlap one day
        if s != covered_end:
            return None
        covered_end = e
    if covered_end != trip_days:
        return None

    # Check each transition has direct flight
    for i in range(len(itinerary_segments_sorted)-1):
        a = itinerary_segments_sorted[i][0]
        b = itinerary_segments_sorted[i+1][0]
        if not edge_exists(build_graph(), a, b):
            return None

    return itinerary_segments_sorted

def main():
    segments = find_itinerary()
    if segments is None:
        print(json.dumps({"itinerary": []}))
        return
    itinerary = []
    for city, s, e in segments:
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()