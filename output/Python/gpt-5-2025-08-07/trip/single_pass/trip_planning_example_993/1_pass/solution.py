import json
from itertools import permutations

def build_graph():
    # Initialize adjacency with empty sets
    cities = [
        "London", "Amsterdam", "Vilnius", "Frankfurt",
        "Riga", "Stockholm", "Bucharest"
    ]
    adj = {c: set() for c in cities}

    def add_edge(a, b, bidirectional=True):
        adj[a].add(b)
        if bidirectional:
            adj[b].add(a)

    # Add bidirectional edges from the problem statement ("X and Y")
    add_edge("London", "Amsterdam", True)
    add_edge("Vilnius", "Frankfurt", True)
    add_edge("Riga", "Stockholm", True)
    add_edge("London", "Bucharest", True)
    add_edge("Amsterdam", "Stockholm", True)
    add_edge("Amsterdam", "Frankfurt", True)
    add_edge("Frankfurt", "Stockholm", True)
    add_edge("Bucharest", "Riga", True)
    add_edge("Amsterdam", "Riga", True)
    add_edge("Amsterdam", "Bucharest", True)
    add_edge("Riga", "Frankfurt", True)
    add_edge("Bucharest", "Frankfurt", True)
    add_edge("London", "Frankfurt", True)
    add_edge("London", "Stockholm", True)
    add_edge("Amsterdam", "Vilnius", True)

    # Add directed edge ("from Riga to Vilnius")
    add_edge("Riga", "Vilnius", bidirectional=False)

    return adj

def compute_schedule(path, durations, total_days):
    # Compute inclusive day ranges for each city along the path with flight-day overlaps
    schedule = {}
    t_curr = 1  # Start on Day 1 in the first city
    for i in range(len(path) - 1):
        city = path[i]
        start = t_curr
        end = start + durations[city] - 1  # flight to next city on 'end' day (counts for both)
        schedule[city] = (start, end)
        t_curr = end  # next city starts on the same day as flight (overlap)
    # Last city runs until the end of the trip
    last_city = path[-1]
    schedule[last_city] = (t_curr, total_days)
    return schedule

def interval_length(interval):
    a, b = interval
    return b - a + 1

def intervals_overlap(i1, i2):
    return not (i1[1] < i2[0] or i2[1] < i1[0])

def contains_days(interval, days):
    a, b = interval
    return all(a <= d <= b for d in days)

def find_itinerary():
    # Input variables (constraints)
    total_days = 15
    city_durations = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,
        "Vilnius": 5,
        "London": 2,
        "Stockholm": 3,
        "Bucharest": 4
    }
    friend_city = "Amsterdam"
    friend_days = [2, 3]  # must be in Amsterdam on both Day 2 and Day 3
    workshop_city = "Vilnius"
    workshop_window = (7, 11)  # inclusive
    wedding_city = "Stockholm"
    wedding_window = (13, 15)  # inclusive

    # Build flight graph
    adj = build_graph()
    cities = list(city_durations.keys())

    # Pre-check feasibility: sum of durations should equal total_days + number_of_flights (6 for 7 cities)
    sum_durations = sum(city_durations.values())
    required_flights = len(cities) - 1
    if sum_durations != total_days + required_flights:
        # If this fails, constraints are inconsistent; but per problem it should hold
        raise ValueError("Duration totals do not align with total days and transitions.")

    # For Amsterdam to include days 2 and 3:
    # - The second city must be Amsterdam
    # - The first city's duration must be exactly 2 so that flight to Amsterdam is on Day 2
    second_city = friend_city
    start_candidates = [c for c, d in city_durations.items() if d == 2 and c != second_city and second_city in adj[c]]

    # The last city must allow attendance of the wedding in days 13-15; with given durations, this is the final city.
    last_city = wedding_city

    # Remaining cities to permute exclude fixed second and fixed last and the chosen start
    def valid_path(path):
        # Check consecutive flights exist
        for a, b in zip(path, path[1:]):
            if b not in adj[a]:
                return False
        # Compute schedule and validate all constraints
        schedule = compute_schedule(path, city_durations, total_days)

        # Validate that computed durations match requested ones
        for c in path:
            if interval_length(schedule[c]) != city_durations[c]:
                return False

        # Friend meeting in Amsterdam on days 2 and 3
        if not contains_days(schedule[friend_city], friend_days):
            return False

        # Workshop in Vilnius between day 7 and day 11 (at least one overlap)
        if not intervals_overlap(schedule[workshop_city], workshop_window):
            return False

        # Wedding in Stockholm between day 13 and day 15 (at least one overlap)
        if not intervals_overlap(schedule[wedding_city], wedding_window):
            return False

        return True

    # Search for a Hamiltonian path matching constraints
    for start in sorted(start_candidates):
        remaining = [c for c in cities if c not in {start, second_city, last_city}]
        # Build permutations of the middle segment
        for middle_perm in permutations(remaining):
            path = [start, second_city] + list(middle_perm) + [last_city]
            if valid_path(path):
                schedule = compute_schedule(path, city_durations, total_days)
                itinerary = []
                for city in path:
                    s, e = schedule[city]
                    itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
                return {"itinerary": itinerary}

    # If no path found, return an empty itinerary (should not happen given the data)
    return {"itinerary": []}

if __name__ == "__main__":
    result = find_itinerary()
    print(json.dumps(result, ensure_ascii=False))