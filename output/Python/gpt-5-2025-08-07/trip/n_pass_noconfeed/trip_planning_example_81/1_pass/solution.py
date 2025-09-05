import json
from typing import Dict, List, Optional, Tuple, Set

def find_itinerary(
    cities: List[str],
    duration_days: int,
    required_stays: Dict[str, int],
    direct_flights: List[Tuple[str, str]],
    conference_city: str,
    conference_days: Set[int],
) -> Optional[List[Dict]]:

    # Build undirected adjacency list for direct flights
    adj = {c: set() for c in cities}
    for a, b in direct_flights:
        if a not in adj:
            adj[a] = set()
        if b not in adj:
            adj[b] = set()
        adj[a].add(b)
        adj[b].add(a)

    # Quick feasibility check for total number of flight days required
    total_required = sum(required_stays.values())
    D = duration_days
    f_required = total_required - D
    if f_required < 0 or f_required > D:
        return None  # Impossible totals

    # DFS search for a valid plan with exactly f_required flight days
    # Each day record will be: {"day": d, "action": "stay"/"fly", "from": cityA, "to": cityB}
    def dfs(
        day: int,
        current_city: str,
        flights_used: int,
        counts: Dict[str, int],
        plan: List[Dict],
    ) -> Optional[List[Dict]]:
        if day > D:
            # All days assigned; check final counts and flights
            if flights_used == f_required and all(counts[c] == required_stays.get(c, 0) for c in cities):
                # Also ensure conference constraints fully satisfied; enforced during recursion
                return plan
            return None

        remaining_days = D - day + 1
        # Prune if not enough days left to allocate required number of flights
        if flights_used > f_required or flights_used + remaining_days < f_required:
            return None

        # Try staying
        # Presence if stay = {current_city}
        if counts[current_city] + 1 <= required_stays.get(current_city, 0):
            presence = {current_city}
            # Check conference presence requirement
            if (day not in conference_days) or (conference_city in presence):
                counts[current_city] += 1
                plan.append({"day": day, "action": "stay", "from": current_city, "to": current_city})
                res = dfs(day + 1, current_city, flights_used, counts, plan)
                if res is not None:
                    return res
                plan.pop()
                counts[current_city] -= 1

        # Try flying to any neighbor (if we still need more flights)
        if flights_used < f_required:
            for neighbor in adj[current_city]:
                # On a flight day, presence = {current_city, neighbor}
                # Update counts cautiously (both cities increment by 1)
                if counts[current_city] + 1 <= required_stays.get(current_city, 0) and counts[neighbor] + 1 <= required_stays.get(neighbor, 0):
                    presence = {current_city, neighbor}
                    if (day not in conference_days) or (conference_city in presence):
                        counts[current_city] += 1
                        counts[neighbor] += 1
                        plan.append({"day": day, "action": "fly", "from": current_city, "to": neighbor})
                        res = dfs(day + 1, neighbor, flights_used + 1, counts, plan)
                        if res is not None:
                            return res
                        plan.pop()
                        counts[current_city] -= 1
                        counts[neighbor] -= 1

        return None

    # Try each city as a possible starting city
    for start_city in cities:
        # Quick prune: if day 1 must be in conference city and start_city doesn't match,
        # we can only satisfy it by flying into conference city on day 1 (which requires a direct flight).
        # The DFS will handle this generally, so we won't over-prune here.
        initial_counts = {c: 0 for c in cities}
        plan: List[Dict] = []
        result = dfs(day=1, current_city=start_city, flights_used=0, counts=initial_counts, plan=plan)
        if result is not None:
            # Convert day-by-day plan into itinerary with day ranges per presence (including flight days counted for both cities)
            # Build chronological events: for each day, one or two entries
            events: List[Tuple[int, int, str]] = []  # (start_day, end_day, place)

            for entry in result:
                d = entry["day"]
                if entry["action"] == "stay":
                    events.append((d, d, entry["from"]))  # "from" == "to"
                else:  # fly
                    events.append((d, d, entry["from"]))  # origin city counts
                    events.append((d, d, entry["to"]))    # destination city counts

            # Merge consecutive events with same place and consecutive days
            merged: List[Tuple[int, int, str]] = []
            for start, end, place in events:
                if merged and merged[-1][2] == place and merged[-1][1] == start - 1:
                    # extend previous
                    prev_start, prev_end, prev_place = merged[-1]
                    merged[-1] = (prev_start, end, prev_place)
                else:
                    merged.append((start, end, place))

            itinerary = []
            for s, e, p in merged:
                if s == e:
                    dr = f"Day {s}-{e}"
                else:
                    dr = f"Day {s}-{e}"
                itinerary.append({"day_range": dr, "place": p})

            return itinerary

    return None


def main():
    # Input variables
    cities = ["Mykonos", "Budapest", "Hamburg"]
    duration_days = 9
    required_stays = {
        "Mykonos": 6,
        "Budapest": 3,
        "Hamburg": 2,
    }
    direct_flights = [
        ("Budapest", "Mykonos"),
        ("Hamburg", "Budapest"),
    ]
    conference_city = "Mykonos"
    conference_days = {4, 9}

    itinerary = find_itinerary(
        cities=cities,
        duration_days=duration_days,
        required_stays=required_stays,
        direct_flights=direct_flights,
        conference_city=conference_city,
        conference_days=conference_days,
    )

    if itinerary is None:
        output = {"itinerary": []}
    else:
        output = {"itinerary": itinerary}

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()