import json
import re

def build_graph(cities, flights_text):
    edges = set()
    for part in flights_text.split(','):
        seg = part.strip().rstrip('.').strip()
        if not seg:
            continue
        if ' and ' in seg:
            a, b = seg.split(' and ', 1)
        elif ' to ' in seg:
            a, b = seg.split(' to ', 1)
            a = a.strip()
            if a.lower().startswith('from '):
                a = a[5:].strip()
        else:
            # Unrecognized pattern; skip
            continue
        a = a.strip()
        b = b.strip()
        # Only keep edges where both endpoints are in the target set of cities
        if a in cities and b in cities:
            edges.add((a, b))
            edges.add((b, a))
    # Build adjacency list
    graph = {c: set() for c in cities}
    for u, v in edges:
        graph[u].add(v)
    return graph

def compute_schedule(order, durations):
    # Given city order and durations, compute inclusive day ranges using overlap rule
    itinerary = []
    s = 1
    for i, city in enumerate(order):
        d = durations[city]
        e = s + d - 1
        itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        s = e  # next city starts on the same day (flight day overlaps)
    return itinerary

def validate_schedule(order, durations, trip_length, constraints):
    # Compute day ranges and validate constraints
    itinerary = compute_schedule(order, durations)
    # Check last day equals trip_length
    last_range = itinerary[-1]["day_range"]
    m = re.match(r"Day (\d+)-(\d+)", last_range)
    if not m:
        return None
    end_day = int(m.group(2))
    if end_day != trip_length:
        return None

    # Build quick lookup for day ranges
    ranges = {item["place"]: tuple(map(int, re.match(r"Day (\d+)-(\d+)", item["day_range"]).groups())) for item in itinerary}

    # Check city-day duration matches
    for city, (s, e) in ranges.items():
        if e - s + 1 != durations[city]:
            return None

    # Validate special constraints
    # Prague must cover days 5-9
    if not (ranges["Prague"][0] <= 5 and ranges["Prague"][1] >= 9):
        return None
    # Split must cover days 11-13
    if not (ranges["Split"][0] <= 11 and ranges["Split"][1] >= 13):
        return None
    # Riga must cover days 15-16
    if not (ranges["Riga"][0] <= 15 and ranges["Riga"][1] >= 16):
        return None
    # Stockholm must cover days 16-17
    if not (ranges["Stockholm"][0] <= 16 and ranges["Stockholm"][1] >= 17):
        return None
    # Vienna must include at least one of days 1-5
    v_s, v_e = ranges["Vienna"]
    if v_e < 1 or v_s > 5:
        return None

    # All good
    return itinerary

def plan_itinerary():
    # Input variables: cities, durations, total trip length, flight network, and constraints
    trip_length = 20
    durations = {
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
    cities = list(durations.keys())

    flights_text = """Riga and Stockholm, Stockholm and Brussels, Istanbul and Munich, Istanbul and Riga, Prague and Split, Vienna and Brussels, Vienna and Riga, Split and Stockholm, Munich and Amsterdam, Split and Amsterdam, Amsterdam and Stockholm, Amsterdam and Riga, Vienna and Stockholm, Vienna and Istanbul, Vienna and Seville, Istanbul and Amsterdam, Munich and Brussels, Prague and Munich, from Riga to Munich, Prague and Amsterdam, Prague and Brussels, Prague and Istanbul, Istanbul and Stockholm, Vienna and Prague, Munich and Split, Vienna and Amsterdam, Prague and Stockholm, Brussels and Seville, Munich and Stockholm, Istanbul and Brussels, Amsterdam and Seville, Vienna and Split, Munich and Seville, Riga and Brussels, Prague and Riga, Vienna and Munich."""
    graph = build_graph(cities, flights_text)

    # Forced start days (must include these days, given durations they become exact starts)
    forced_starts = {
        "Prague": 5,      # Days 5-9
        "Split": 11,      # Days 11-13
        "Riga": 15,       # Days 15-16
        "Stockholm": 16,  # Days 16-17
    }
    S_target = {c: start - 1 for c, start in forced_starts.items()}  # cumulative sum of (d-1) before the city

    # Helper for cumulative sum of (d-1)
    def d_minus_1(c): return durations[c] - 1

    N = len(cities)

    # Candidate priority order to guide search (heuristic)
    candidate_priority = ["Vienna", "Prague", "Amsterdam", "Istanbul", "Munich", "Split", "Riga", "Stockholm", "Brussels", "Seville"]

    def backtrack(seq, used, cumS):
        # Prune: if Vienna not yet placed and cumS > 4, Vienna cannot intersect days 1-5 anymore
        if "Vienna" not in used and cumS > 4:
            return None
        # Prune: cannot overshoot any forced start's S_target before placing it
        for z, st in S_target.items():
            if z not in used and cumS > st:
                return None
        # If we are exactly at an S_target before placing that city, the next must be that city
        must_place = None
        for z, st in sorted(S_target.items(), key=lambda x: x[1]):  # deterministic
            if z not in used and st == cumS:
                must_place = z
                break

        if len(seq) == N:
            # Validate full itinerary
            itinerary = validate_schedule(seq, durations, trip_length, forced_starts)
            if itinerary is not None:
                return itinerary
            return None

        # Build candidate list
        candidates = [c for c in candidate_priority if c not in used]
        for c in candidates:
            # Must place specific city if required at this cumulative S
            if must_place is not None and c != must_place:
                continue
            # Adjacency constraint
            if seq:
                prev = seq[-1]
                if c not in graph.get(prev, set()):
                    continue
            s = 1 + cumS
            # Forced start cities must start at exact required day
            if c in forced_starts and s != forced_starts[c]:
                continue

            new_cumS = cumS + d_minus_1(c)

            # Prune overshoot after adding this city
            overshoot = False
            for z, st in S_target.items():
                if z not in used and z != c and new_cumS > st:
                    overshoot = True
                    break
            if overshoot:
                continue

            # Additional Vienna prune: if Vienna not yet placed and c != Vienna and new_cumS > 4, skip
            if "Vienna" not in used and c != "Vienna" and new_cumS > 4:
                continue

            seq.append(c)
            used.add(c)
            result = backtrack(seq, used, new_cumS)
            if result is not None:
                return result
            used.remove(c)
            seq.pop()
        return None

    itinerary = backtrack([], set(), 0)
    if itinerary is None:
        # Fallback: no solution found (should not happen with given data)
        itinerary = [{"day_range": "Day 1-20", "place": "Itinerary not found with given constraints"}]

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_itinerary()
    print(json.dumps(result, ensure_ascii=False))