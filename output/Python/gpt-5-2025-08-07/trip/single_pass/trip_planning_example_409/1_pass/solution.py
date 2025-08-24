import json

def plan_trip():
    # Input variables based on the given constraints
    total_days = 12
    cities = ["Zurich", "Hamburg", "Helsinki", "Bucharest", "Split"]
    required_days = {
        "Zurich": 3,
        "Hamburg": 2,
        "Helsinki": 2,
        "Bucharest": 2,
        "Split": 7,
    }
    # Direct flights (undirected edges)
    direct_pairs = [
        ("Zurich", "Helsinki"),
        ("Hamburg", "Bucharest"),
        ("Helsinki", "Hamburg"),
        ("Zurich", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Split"),
        ("Helsinki", "Split"),
        ("Split", "Hamburg"),
    ]
    # Build adjacency map
    neighbors = {c: set() for c in cities}
    for a, b in direct_pairs:
        neighbors[a].add(b)
        neighbors[b].add(a)
    # Special day constraints
    wedding_city = "Zurich"
    wedding_days_window = {1, 2, 3}  # must include Zurich on at least one of these days
    conference_city = "Split"
    conference_days = {4, 10}  # must include Split on these days

    # Derived constraints
    sum_required = sum(required_days.values())
    required_flight_days = sum_required - total_days  # By overlap rule

    # DFS search with pruning
    def dfs(day, current_city, counts, wedding_satisfied, flights_used, actions):
        # If done
        if day > total_days:
            # Check all constraints satisfied
            if (wedding_satisfied and
                all(counts[c] == required_days[c] for c in cities) and
                flights_used == required_flight_days):
                return actions
            return None

        # Prune if any count exceeds required
        if any(counts[c] > required_days[c] for c in cities):
            return None

        # If wedding window passed, ensure satisfied
        if day > max(wedding_days_window) and not wedding_satisfied:
            return None

        # Remaining counts / days feasibility checks
        remaining_days = total_days - day + 1
        remaining_counts_sum = sum(required_days[c] - counts[c] for c in cities)
        needed_flights_left = remaining_counts_sum - remaining_days
        # Each remaining day gives at most 2 counts (if a flight), so exact equation must hold non-negatively
        if needed_flights_left < 0 or needed_flights_left > remaining_days:
            return None
        # Also, per-city remaining must not exceed remaining calendar days (a city can appear at most once per day)
        for c in cities:
            if required_days[c] - counts[c] > remaining_days:
                return None

        # Build action list depending on special day constraints (conference)
        actions_today = []

        is_conference_day = day in conference_days
        if is_conference_day:
            if current_city == conference_city:
                # Option 1: stay in Split
                actions_today.append(("stay", current_city))
                # Option 2: fly out of Split (still present in Split that day)
                for nb in sorted(neighbors[current_city]):
                    actions_today.append(("flight", current_city, nb))
            else:
                # Must include Split today -> only option is to fly to Split if direct
                if conference_city in neighbors[current_city]:
                    actions_today.append(("flight", current_city, conference_city))
                else:
                    return None  # impossible to include Split today
        else:
            # Normal day: can stay or take a direct flight
            actions_today.append(("stay", current_city))
            for nb in sorted(neighbors[current_city]):
                actions_today.append(("flight", current_city, nb))

        # Try each action
        for act in actions_today:
            if act[0] == "stay":
                _, frm = act
                new_counts = dict(counts)
                new_counts[frm] += 1
                new_wedding = wedding_satisfied or (day in wedding_days_window and frm == wedding_city)
                new_flights_used = flights_used
                next_city = frm
                label = frm
                # Per-city feasibility prune after update
                remaining_days_after = total_days - day
                if any(required_days[c] - new_counts[c] > remaining_days_after for c in cities):
                    continue
                res = dfs(day + 1, next_city, new_counts, new_wedding, new_flights_used, actions + [(day, label)])
                if res:
                    return res
            else:
                _, frm, to = act
                new_counts = dict(counts)
                new_counts[frm] += 1
                new_counts[to] += 1
                new_wedding = wedding_satisfied or (day in wedding_days_window and (frm == wedding_city or to == wedding_city))
                new_flights_used = flights_used + 1
                if new_flights_used > required_flight_days:
                    continue
                next_city = to
                label = f"{frm} -> {to} (flight day)"
                # Prune per-city feasibility after update
                remaining_days_after = total_days - day
                if any(required_days[c] - new_counts[c] > remaining_days_after for c in cities):
                    continue
                # Prune if any city exceeds required
                if any(new_counts[c] > required_days[c] for c in cities):
                    continue
                res = dfs(day + 1, next_city, new_counts, new_wedding, new_flights_used, actions + [(day, label)])
                if res:
                    return res

        return None

    # Initialize and search starting from Zurich (logical for wedding)
    start_city = "Zurich"
    initial_counts = {c: 0 for c in cities}
    solution_actions = dfs(
        day=1,
        current_city=start_city,
        counts=initial_counts,
        wedding_satisfied=False,
        flights_used=0,
        actions=[]
    )

    if not solution_actions:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    # Convert daily actions to compressed day ranges
    day_labels = [label for (_, label) in sorted(solution_actions, key=lambda x: x[0])]

    itinerary = []
    start = 1
    current_label = day_labels[0]
    for i in range(2, total_days + 1):
        if day_labels[i - 1] != current_label:
            if start == i - 1:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{i - 1}"
            itinerary.append({"day_range": day_range, "place": current_label})
            start = i
            current_label = day_labels[i - 1]
    # Append last range
    if start == total_days:
        day_range = f"Day {start}"
    else:
        day_range = f"Day {start}-{total_days}"
    itinerary.append({"day_range": day_range, "place": current_label})

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, ensure_ascii=False))