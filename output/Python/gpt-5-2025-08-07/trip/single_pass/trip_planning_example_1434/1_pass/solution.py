import json
import re
from collections import defaultdict

def build_adjacency(edges_text):
    # Parse "CityA and CityB" pairs and build undirected adjacency
    adj = defaultdict(set)
    # Split by commas, strip whitespace and trailing periods
    parts = [p.strip().rstrip('.') for p in edges_text.split(',')]
    for p in parts:
        if not p:
            continue
        # Expect format "CityA and CityB"
        m = re.match(r'(.+?)\s+and\s+(.+)$', p)
        if m:
            a = m.group(1).strip()
            b = m.group(2).strip()
            adj[a].add(b)
            adj[b].add(a)
    return adj

def compute_itinerary(cities_durations, edges_text, total_days, total_cities,
                      pinned_starts, wedding_city, wedding_range,
                      meet_city, meet_range, conference_city, conference_range):
    cities = list(cities_durations.keys())
    assert len(cities) == total_cities, "City count mismatch with total_cities"
    adj = build_adjacency(edges_text)

    # Helper to check adjacency existence for all cities
    for c in cities:
        if c not in adj:
            adj[c] = set()  # allow isolated (though search will fail if used)

    durations = cities_durations.copy()

    # Backtracking to find valid order and day ranges
    best_schedule = []

    # Prepare fast lookups for constraints
    pinned_starts = pinned_starts.copy()  # {'Frankfurt':1, 'Mykonos':10, 'Seville':13}
    required_start_myko = pinned_starts.get(meet_city, None)
    required_start_seville = pinned_starts.get(conference_city, None)

    def next_start_day_for(schedule):
        if not schedule:
            return 1
        # next start is previous end (overlap on travel day)
        return schedule[-1][2]

    def can_place(city, schedule):
        # First city must be wedding_city (Frankfurt)
        if not schedule and city != wedding_city:
            return False
        # Adjacency requirement (only direct flights)
        if schedule:
            prev_city = schedule[-1][0]
            if city not in adj[prev_city]:
                return False
        # Start day constraints
        start_day = next_start_day_for(schedule)

        # If a city has a pinned start, enforce it
        if city in pinned_starts and pinned_starts[city] != start_day:
            return False

        # If it's exactly the pinned start for Mykonos or Seville, enforce picking them at that moment
        if required_start_myko is not None and start_day == required_start_myko and city != meet_city and all(c != meet_city for c,_,_ in schedule):
            return False
        if required_start_seville is not None and start_day == required_start_seville and city != conference_city and all(c != conference_city for c,_,_ in schedule):
            return False

        # If we've passed the required start for Mykonos or Seville without placing them, prune
        if required_start_myko is not None and start_day > required_start_myko and all(c != meet_city for c,_,_ in schedule):
            return False
        if required_start_seville is not None and start_day > required_start_seville and all(c != conference_city for c,_,_ in schedule):
            return False

        return True

    def validate_final(schedule):
        # Must include all cities exactly once
        if len(schedule) != total_cities:
            return False

        # Check total days (end day of last city)
        last_end = schedule[-1][2]
        if last_end != total_days:
            return False

        # Verify durations
        for city, start, end in schedule:
            if end - start + 1 != durations[city]:
                return False

        # Wedding in Frankfurt between day 1 and 5 inclusive
        for city, start, end in schedule:
            if city == wedding_city:
                if start > wedding_range[1] or end < wedding_range[0]:
                    return False
                # Must exactly be days 1-5 per planning here
                if start != 1 or end != 5:
                    return False

        # Meet friends at Mykonos between day 10 and 11
        for city, start, end in schedule:
            if city == meet_city:
                if start != meet_range[0] or end != meet_range[1]:
                    return False

        # Conference in Seville day 13-17
        for city, start, end in schedule:
            if city == conference_city:
                if start != conference_range[0] or end != conference_range[1]:
                    return False

        # Check direct flights for each transition
        for i in range(1, len(schedule)):
            a = schedule[i-1][0]
            b = schedule[i][0]
            if b not in adj[a]:
                return False

        return True

    # Order candidate selection with a heuristic to reduce branching
    def candidate_ordering(remaining, schedule):
        start_day = next_start_day_for(schedule)
        # If next start matches pinned starts, try that city first
        priority = []
        others = []
        for c in remaining:
            if c in pinned_starts and pinned_starts[c] == start_day:
                priority.append(c)
            else:
                others.append(c)
        # Heuristic: prefer cities adjacent to Mykonos or Seville if we are before those starts
        def score(city):
            s = 0
            # adjacency to previous city already required; favor shorter durations before tight windows
            s -= durations[city]  # prefer shorter before tight deadlines
            if city in adj[meet_city]: s += 1
            if city in adj[conference_city]: s += 1
            return -s  # negative for ascending order
        others_sorted = sorted(others, key=score)
        return priority + others_sorted

    def backtrack(schedule, remaining):
        nonlocal best_schedule
        if best_schedule:
            return  # stop at first found feasible schedule

        if not remaining:
            if validate_final(schedule):
                best_schedule = schedule[:]
            return

        start_day = next_start_day_for(schedule)

        # Early pruning: if start_day exceeds total_days, fail
        if start_day > total_days:
            return

        # Early pruning for pinned cities that must still be placed
        if required_start_myko is not None and start_day > required_start_myko and all(c != meet_city for c,_,_ in schedule):
            return
        if required_start_seville is not None and start_day > required_start_seville and all(c != conference_city for c,_,_ in schedule):
            return

        for city in candidate_ordering(remaining, schedule):
            if not can_place(city, schedule):
                continue
            # Place city
            start = start_day
            end = start + durations[city] - 1
            # Another pruning: end cannot exceed total_days if this is the last city; otherwise it's fine because overlaps reduce total days
            # But by construction, the final end will be total_days.
            new_schedule = schedule + [(city, start, end)]
            # Ensure we can still fit remaining pinned starts in the future:
            # If we just placed city and the next_start becomes some value incompatible with upcoming pins, the recursion will prune itself.
            new_remaining = [r for r in remaining if r != city]
            backtrack(new_schedule, new_remaining)
            if best_schedule:
                return

    # Initialize
    all_cities = set(cities_durations.keys())
    remaining = list(all_cities)
    # Start with wedding city first
    first_city = wedding_city
    remaining.remove(first_city)
    initial_schedule = [(first_city, 1, durations[first_city])]  # Frankfurt 1-5 enforced by durations
    # Adjust end of Frankfurt to ensure it's 1-5
    initial_schedule[0] = (first_city, 1, 1 + durations[first_city] - 1)

    backtrack(initial_schedule, remaining)

    if not best_schedule:
        raise RuntimeError("No feasible itinerary found under given constraints.")

    # Build JSON output
    itinerary = []
    for city, start, end in best_schedule:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    return {"itinerary": itinerary}

def main():
    # Input variables based on the problem statement
    total_days = 23
    total_cities = 10

    cities_durations = {
        "Rome": 3,
        "Mykonos": 2,
        "Lisbon": 2,
        "Frankfurt": 5,
        "Nice": 3,
        "Stuttgart": 4,
        "Venice": 4,
        "Dublin": 2,
        "Bucharest": 2,
        "Seville": 5
    }

    edges_text = (
        "Rome and Stuttgart, Venice and Rome, Dublin and Bucharest, Mykonos and Rome, "
        "Seville and Lisbon, Frankfurt and Venice, Venice and Stuttgart, Bucharest and Lisbon, "
        "Nice and Mykonos, Venice and Lisbon, Dublin and Lisbon, Venice and Dublin, "
        "Rome and Seville, Frankfurt and Rome, Nice and Dublin, Rome and Bucharest, "
        "Frankfurt and Dublin, Rome and Dublin, Venice and Dublin, Rome and Lisbon, "
        "Frankfurt and Lisbon, Nice and Rome, Frankfurt and Nice, Frankfurt and Stuttgart, "
        "Frankfurt and Bucharest, Lisbon and Stuttgart, Nice and Lisbon, Seville and Dublin."
    )

    # Pinned start days for certain cities:
    pinned_starts = {
        "Frankfurt": 1,   # Wedding city starts at Day 1 by plan
        "Mykonos": 10,    # Meet friends in Mykonos between Day 10 and 11
        "Seville": 13     # Conference in Seville during Day 13 to Day 17
    }

    wedding_city = "Frankfurt"
    wedding_range = (1, 5)  # Must be in Frankfurt between day 1 and 5
    meet_city = "Mykonos"
    meet_range = (10, 11)   # Be in Mykonos day 10-11
    conference_city = "Seville"
    conference_range = (13, 17)  # Be in Seville day 13-17

    result = compute_itinerary(
        cities_durations=cities_durations,
        edges_text=edges_text,
        total_days=total_days,
        total_cities=total_cities,
        pinned_starts=pinned_starts,
        wedding_city=wedding_city,
        wedding_range=wedding_range,
        meet_city=meet_city,
        meet_range=meet_range,
        conference_city=conference_city,
        conference_range=conference_range
    )

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()