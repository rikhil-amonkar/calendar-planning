def main():
    # Input variables (trip constraints)
    total_days = 17
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    durations = {
        "Mykonos": 3,
        "Riga": 3,
        "Munich": 4,
        "Bucharest": 4,
        "Rome": 4,
        "Nice": 3,
        "Krakow": 2,
    }
    # Event constraints
    must_include = {
        "Rome": {1, 4},      # Conference on Day 1 and Day 4 in Rome
    }
    exact_block = {
        "Mykonos": (4, 6),   # Wedding in Mykonos Days 4-6; and 3 days total there
        "Krakow": (16, 17),  # Annual show Days 16-17; and 2 days total there
    }

    adjacency = build_adjacency()

    # We will search for an order that:
    # - Starts with Rome (to include Day 1)
    # - Has Mykonos as second city (to start at Day 4 when Rome ends on Day 4)
    # - Ends with Krakow (to include Days 16-17)
    # - Uses only direct flights
    # - Satisfies all day constraints via contiguous blocks with overlaps on flight days

    start_city = "Rome"
    end_city = "Krakow"
    must_be_second = "Mykonos"

    remaining_cities = [c for c in cities if c not in {start_city, end_city}]
    if must_be_second in remaining_cities:
        remaining_cities.remove(must_be_second)

    found_schedule = None

    # We fix: [Rome] + [Mykonos] + perm(remaining_without_munich) + [Munich] + [Krakow]
    # because Krakow only connects from Munich and we need Krakow at the end.
    # So ensure Munich is just before Krakow.
    middle_fixed_end = "Munich"
    if middle_fixed_end in remaining_cities:
        remaining_cities.remove(middle_fixed_end)

    for perm in permutations(remaining_cities):  # permutes Nice, Riga, Bucharest
        order = [start_city, must_be_second] + list(perm) + [middle_fixed_end, end_city]

        # Quick adjacency feasibility check
        feasible_edges = True
        for i in range(len(order) - 1):
            a, b = order[i], order[i + 1]
            if b not in adjacency.get(a, set()):
                feasible_edges = False
                break
        if not feasible_edges:
            continue

        schedule = compute_schedule(order, durations, start_day=1)

        constraints = {
            "total_days": total_days,
            "must_include": must_include,
            "exact_block": exact_block,
        }
        if validate_schedule(schedule, adjacency, constraints):
            found_schedule = schedule
            break

    if not found_schedule:
        raise RuntimeError("No valid itinerary found under given constraints.")

    # Build the JSON output
    itinerary = []
    for city, start, end in found_schedule:
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})

    output = {"itinerary": itinerary}
    print(json.dumps(output))