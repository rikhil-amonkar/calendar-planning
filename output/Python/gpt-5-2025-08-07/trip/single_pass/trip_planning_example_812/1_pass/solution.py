import json
import itertools

def build_directed_edges():
    # Build directed adjacency set based on given direct flights
    edges = set()
    def add_bidirectional(a, b):
        edges.add((a, b))
        edges.add((b, a))
    def add_one_way(a, b):
        edges.add((a, b))

    # Bidirectional connections
    add_bidirectional("Florence", "Vienna")
    add_bidirectional("Paris", "Warsaw")
    add_bidirectional("Munich", "Vienna")
    add_bidirectional("Porto", "Vienna")
    add_bidirectional("Warsaw", "Vienna")
    add_bidirectional("Munich", "Warsaw")
    add_bidirectional("Munich", "Nice")
    add_bidirectional("Paris", "Florence")
    add_bidirectional("Warsaw", "Nice")
    add_bidirectional("Porto", "Munich")
    add_bidirectional("Porto", "Nice")
    add_bidirectional("Paris", "Vienna")
    add_bidirectional("Nice", "Vienna")
    add_bidirectional("Porto", "Paris")
    add_bidirectional("Paris", "Nice")
    add_bidirectional("Paris", "Munich")
    add_bidirectional("Porto", "Warsaw")

    # One-way connection
    add_one_way("Florence", "Munich")

    return edges

def compute_itinerary():
    # Input variables: city stay targets and presence constraints
    cities = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
    target_days = {
        "Paris": 5,
        "Florence": 3,
        "Vienna": 2,
        "Porto": 3,
        "Munich": 5,
        "Nice": 5,
        "Warsaw": 3
    }
    # Presence constraints: inclusive day ranges that must be covered (present)
    presence_requirements = {
        "Porto": [(1, 3)],      # workshop days 1-3
        "Warsaw": [(13, 15)],   # wedding days 13-15
        "Vienna": [(19, 20)]    # relatives days 19-20
    }

    total_days = 20
    first_city = "Porto"
    last_city = "Vienna"

    edges = build_directed_edges()

    # Derive assigned-day duration (without counting departure-day overlap)
    def assigned_duration(city):
        # For last city, assigned duration equals target (no outbound overlap)
        if city == last_city:
            return target_days[city]
        else:
            return target_days[city] - 1

    # Generate orders: first fixed, last fixed, permute the middle
    middle_cities = [c for c in cities if c not in (first_city, last_city)]
    best_order = None
    best_schedule = None

    for perm in itertools.permutations(middle_cities):
        order = [first_city] + list(perm) + [last_city]

        # Check adjacency feasibility first
        ok_edges = True
        for a, b in zip(order[:-1], order[1:]):
            if (a, b) not in edges:
                ok_edges = False
                break
        if not ok_edges:
            continue

        # Compute start days s[i] for each city in order
        starts = [None] * len(order)
        starts[0] = 1
        feasible = True
        for i in range(len(order) - 1):
            c = order[i]
            dur_assign = assigned_duration(c)
            next_start = starts[i] + dur_assign
            starts[i + 1] = next_start

        # End must align to 20 with last city's assigned duration
        last_start = starts[-1]
        last_assigned = assigned_duration(last_city)
        if last_start != total_days - last_assigned + 1:
            continue  # timing doesn't align to 20 days

        # Build assignment: which city is assigned on each day
        day_to_city = {}
        segments = []  # (city, start, end_assigned)
        for i, c in enumerate(order):
            start = starts[i]
            if i < len(order) - 1:
                end = starts[i + 1] - 1
            else:
                end = total_days
            segments.append((c, start, end))
            for d in range(start, end + 1):
                if d < 1 or d > total_days:
                    feasible = False
                    break
                day_to_city[d] = c
            if not feasible:
                break
        if not feasible:
            continue

        # Compute presence sets per city using flight-day double count rule
        presence = {c: set() for c in order}
        # Assigned presence
        for c, s, e in segments:
            for d in range(s, e + 1):
                presence[c].add(d)
        # Departure-day presence for previous city: on day starts[i] for i>0
        for i in range(1, len(order)):
            prev_c = order[i - 1]
            flight_day = starts[i]
            presence[prev_c].add(flight_day)

        # Validate exact target counts
        exact_counts_ok = True
        for c in cities:
            if len(presence.get(c, set())) != target_days[c]:
                exact_counts_ok = False
                break
        if not exact_counts_ok:
            continue

        # Validate presence requirements
        req_ok = True
        for c, ranges in presence_requirements.items():
            for a, b in ranges:
                for d in range(a, b + 1):
                    if d not in presence[c]:
                        req_ok = False
                        break
                if not req_ok:
                    break
            if not req_ok:
                break
        if not req_ok:
            continue

        # If we reached here, we found a valid plan
        best_order = order
        best_schedule = segments
        break

    if best_schedule is None:
        return {"error": "No valid itinerary found under given constraints."}

    # Build output in desired JSON structure
    itinerary = []
    for c, s, e in best_schedule:
        day_range = f"Day {s}-{e}"
        itinerary.append({"day_range": day_range, "place": c})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))