import json
from itertools import permutations

def find_itinerary():
    # Cities and required stays (in days)
    durations = {
        "Reykjavik": 2,
        "Stuttgart": 5,
        "Oslo": 5,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3,
        "Tallinn": 5,
        "Stockholm": 3,
    }

    # Direct flight pairs (undirected)
    edges = {
        ("Reykjavik", "Stuttgart"),
        ("Reykjavik", "Stockholm"),
        ("Reykjavik", "Tallinn"),
        ("Stockholm", "Oslo"),
        ("Stuttgart", "Porto"),
        ("Oslo", "Split"),
        ("Stockholm", "Stuttgart"),
        ("Reykjavik", "Oslo"),
        ("Oslo", "Geneva"),
        ("Stockholm", "Split"),
        ("Split", "Stuttgart"),
        ("Tallinn", "Oslo"),
        ("Stockholm", "Geneva"),
        ("Oslo", "Porto"),
        ("Geneva", "Porto"),
        ("Geneva", "Split"),
        ("Stockholm", "Tallinn"),  # included based on provided connectivity list
    }

    # Build undirected adjacency for quick lookup
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)

    cities = list(durations.keys())
    start_city = "Reykjavik"
    end_city = "Porto"

    # Sanity totals: sum of city-days should equal total_days + (number_of_flights)
    total_days = 21
    city_days_sum = sum(durations.values())
    num_cities = len(cities)
    required_flights = num_cities - 1
    if city_days_sum != total_days + required_flights:
        # The overlapping day rule implies this equality for a valid linear route
        return None

    middle_cities = [c for c in cities if c not in (start_city, end_city)]

    def compute_schedule(seq):
        schedule = {}
        current_start = 1
        prev_end = None
        for city in seq:
            if prev_end is None:
                s = current_start
            else:
                s = prev_end  # overlap flight day counts for both cities
            e = s + durations[city] - 1
            schedule[city] = (s, e)
            prev_end = e
        return schedule

    def valid_flights(seq):
        for i in range(len(seq) - 1):
            a, b = seq[i], seq[i+1]
            if b not in adj.get(a, set()):
                return False
        return True

    def intersects(r1, r2):
        a1, a2 = r1
        b1, b2 = r2
        return max(a1, b1) <= min(a2, b2)

    # Search for a feasible sequence satisfying all constraints
    for perm in permutations(middle_cities):
        seq = [start_city] + list(perm) + [end_city]
        if not valid_flights(seq):
            continue

        schedule = compute_schedule(seq)

        # Final day must be 21
        last_end = schedule[end_city][1]
        if last_end != total_days:
            continue

        # Conference in Reykjavik on days 1 and 2
        r_s, r_e = schedule["Reykjavik"]
        if not (r_s <= 1 <= r_e and r_s <= 2 <= r_e):
            continue

        # Workshop in Porto between day 19 and day 21 inclusive (Porto must cover 19-21)
        p_s, p_e = schedule["Porto"]
        if not (p_s <= 19 and p_e >= 21):
            continue

        # Meet a friend in Stockholm between day 2 and day 4 (at least one day overlap)
        st_s, st_e = schedule["Stockholm"]
        if not intersects((st_s, st_e), (2, 4)):
            continue

        # If we reach here, we have a feasible solution
        itinerary = []
        for city in seq:
            s, e = schedule[city]
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        return {"itinerary": itinerary}

    return None

def main():
    result = find_itinerary()
    if result is None:
        # If no solution found under the given constraints, output an empty itinerary with a message
        output = {"itinerary": [], "note": "No feasible itinerary found with the given constraints and direct flights."}
    else:
        output = result
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()