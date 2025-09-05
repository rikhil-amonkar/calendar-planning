import json

def parse_flights(text):
    # Build directed adjacency from flight description text
    adj = {}
    def add_edge(a, b):
        adj.setdefault(a, set()).add(b)

    items = [itm.strip() for itm in text.strip().split(",")]
    for raw in items:
        if not raw:
            continue
        s = raw.strip()
        if s.endswith("."):
            s = s[:-1].strip()
        if s.lower().startswith("from "):
            # from X to Y
            s2 = s[5:].strip()  # remove 'from '
            if " to " not in s2:
                continue
            a, b = [x.strip() for x in s2.split(" to ", 1)]
            add_edge(a, b)
        elif " and " in s:
            a, b = [x.strip() for x in s.split(" and ", 1)]
            add_edge(a, b)
            add_edge(b, a)
    return adj

def find_itinerary(cities, durations, windows, adj, total_days=30):
    # Anchored-window segment solver:
    # - Treat window cities as milestones with fixed arrival/departure
    # - Fill each gap with a sequence of cities whose (d-1) contributions
    #   sum to the exact day delta, while respecting directed flights
    all_cities = set(cities)

    # Validate windows against durations and sort by arrival day
    milestones = []
    for city, (arr, dep) in windows.items():
        if city not in durations:
            return None
        if dep - arr + 1 != durations[city]:
            return None
        milestones.append((city, arr, dep))
    milestones.sort(key=lambda x: x[1])  # by arrival day

    # Helper to check flight existence (no restriction for starting city)
    def has_edge(a, b):
        if a is None:
            return True
        return b in adj.get(a, set())

    # Fill a segment from cur_day to target_arrival with non-window cities
    # respecting adjacency, exact day delta, and preparing to connect to next_city.
    from functools import lru_cache

    window_cities = {m[0] for m in milestones}

    @lru_cache(maxsize=None)
    def fill_segment(last_city, cur_day, target_arrival, next_city, used_mask_tuple):
        # used_mask_tuple is a tuple of sorted used cities to allow caching
        used = set(used_mask_tuple)

        # If we're already at the target arrival day, just ensure we can connect to the next city
        if cur_day == target_arrival:
            if next_city is None or has_edge(last_city, next_city):
                return []
            return None

        needed = target_arrival - cur_day  # we need sum(d-1) == needed over this segment

        # Candidates are non-window cities not yet used
        candidates = [c for c in all_cities if c not in used and c not in window_cities]

        # Small heuristic: try cities with larger (d-1) first to reach target faster
        candidates.sort(key=lambda c: -(durations[c] - 1))

        for city in candidates:
            if not has_edge(last_city, city):
                continue
            d = durations[city]
            add = d - 1
            if add <= 0 or add > needed:
                continue
            arrival = cur_day
            depart = arrival + d - 1
            # If this city ends exactly at the target arrival, it must connect to the next city
            if depart == target_arrival and next_city is not None and not has_edge(city, next_city):
                continue

            new_used = tuple(sorted(used | {city}))
            tail = fill_segment(city, depart, target_arrival, next_city, new_used)
            if tail is not None:
                return [(city, arrival, depart)] + tail

        return None

    # Build the full itinerary
    used = set()
    itinerary = []
    cur_day = 1
    last_city = None

    for i, (m_city, m_arr, m_dep) in enumerate(milestones):
        # Fill the gap before this milestone
        seg = fill_segment(last_city, cur_day, m_arr, m_city, tuple(sorted(used)))
        if seg is None:
            return None
        itinerary.extend(seg)
        used.update(c for c, _, _ in seg)

        # Place the milestone city
        if not has_edge(itinerary[-1][0] if itinerary else None, m_city):
            # If there's no preceding segment (start) we still allow starting at the milestone,
            # but then cur_day must already equal m_arr; if not, no solution.
            if not itinerary and cur_day == m_arr:
                pass
            else:
                return None

        # Verify arrival matches window and append milestone block
        if m_arr != (cur_day):
            # Our model requires the milestone arrival to equal the current day pointer
            # which is the depart day of the previous city/segment.
            return None
        if m_dep - m_arr + 1 != durations[m_city]:
            return None

        itinerary.append((m_city, m_arr, m_dep))
        used.add(m_city)
        last_city = m_city
        cur_day = m_dep  # next arrival equals this departure

    # After last milestone, fill to total_days
    final_seg = fill_segment(last_city, cur_day, total_days, None, tuple(sorted(used)))
    if final_seg is None:
        return None
    itinerary.extend(final_seg)
    used.update(c for c, _, _ in final_seg)

    # Ensure every city is used exactly once
    if used != all_cities:
        return None

    # Build output structure
    out = []
    for city, start, end in itinerary:
        out.append({"day_range": f"Day {start}-{end}", "place": city})
    return out

def main():
    total_days = 30
    cities = [
        "Santorini",
        "Krakow",
        "Paris",
        "Vilnius",
        "Munich",
        "Geneva",
        "Amsterdam",
        "Budapest",
        "Split",
    ]
    durations = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4,
    }
    windows = {
        # arrival, departure (inclusive)
        "Paris": (11, 15),
        "Krakow": (18, 22),
        "Santorini": (25, 29),
    }
    flights_text = """
    Paris and Krakow, Paris and Amsterdam, Paris and Split, from Vilnius to Munich, Paris and Geneva,
    Amsterdam and Geneva, Munich and Split, Split and Krakow, Munich and Amsterdam, Budapest and Amsterdam,
    Split and Geneva, Vilnius and Split, Munich and Geneva, Munich and Krakow, from Krakow to Vilnius,
    Vilnius and Amsterdam, Budapest and Paris, Krakow and Amsterdam, Vilnius and Paris, Budapest and Geneva,
    Split and Amsterdam, Santorini and Geneva, Amsterdam and Santorini, Munich and Budapest, Munich and Paris.
    """

    adj = parse_flights(flights_text)

    itinerary = find_itinerary(set(cities), durations, windows, adj, total_days=total_days)
    if itinerary is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()