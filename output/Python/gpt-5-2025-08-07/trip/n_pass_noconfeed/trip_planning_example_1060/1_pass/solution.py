import json
from itertools import permutations

def build_adjacency():
    # Directed adjacency based on provided direct flights
    adj = {}
    def add_edge(a, b, bidirectional=False):
        adj.setdefault(a, set()).add(b)
        if bidirectional:
            adj.setdefault(b, set()).add(a)

    # Add direct flights (bidirectional unless specified "from A to B")
    add_edge("Geneva", "Istanbul", bidirectional=True)
    add_edge("Reykjavik", "Munich", bidirectional=True)
    add_edge("Stuttgart", "Valencia", bidirectional=True)
    add_edge("Reykjavik", "Stuttgart", bidirectional=False)  # one-way
    add_edge("Stuttgart", "Istanbul", bidirectional=True)
    add_edge("Munich", "Geneva", bidirectional=True)
    add_edge("Istanbul", "Vilnius", bidirectional=True)
    add_edge("Valencia", "Seville", bidirectional=True)
    add_edge("Valencia", "Istanbul", bidirectional=True)
    add_edge("Vilnius", "Munich", bidirectional=False)  # one-way
    add_edge("Seville", "Munich", bidirectional=True)
    add_edge("Munich", "Istanbul", bidirectional=True)
    add_edge("Valencia", "Geneva", bidirectional=True)
    add_edge("Valencia", "Munich", bidirectional=True)
    return adj

def compute_schedule(sequence, durations):
    # Schedule using rule: next city starts on the previous city's end day (flight day overlaps)
    schedule = {}
    current_start = 1
    for i, city in enumerate(sequence):
        start = current_start if i == 0 else schedule[sequence[i-1]]["end"]
        end = start + durations[city] - 1
        schedule[city] = {"start": start, "end": end}
        current_start = start  # current_start is always previous end for next iteration
    return schedule

def satisfies_constraints(schedule, constraints):
    # Check hard date windows
    for city, window in constraints.get("fixed_windows", {}).items():
        s, e = window
        if city not in schedule:
            return False
        if not (schedule[city]["start"] == s and schedule[city]["end"] == e):
            return False

    # Check inclusion days
    for city, days in constraints.get("must_include_days", {}).items():
        if city not in schedule:
            return False
        s, e = schedule[city]["start"], schedule[city]["end"]
        for d in days:
            if not (s <= d <= e):
                return False

    return True

def is_flight_path_valid(sequence, adjacency):
    # Ensure each transition is a valid direct flight in the correct direction
    for i in range(len(sequence) - 1):
        a, b = sequence[i], sequence[i+1]
        if b not in adjacency.get(a, set()):
            return False
    return True

def main():
    # Input variables (trip constraints)
    trip_length = 25
    cities = [
        "Stuttgart", "Istanbul", "Vilnius", "Seville",
        "Geneva", "Valencia", "Munich", "Reykjavik"
    ]
    durations = {
        "Stuttgart": 4,
        "Istanbul": 4,
        "Vilnius": 4,
        "Seville": 3,
        "Geneva": 5,
        "Valencia": 5,
        "Munich": 3,
        "Reykjavik": 4
    }
    constraints = {
        # Hard windows that must match exactly
        "fixed_windows": {
            "Reykjavik": (1, 4),    # Workshop between day 1 and day 4
            "Munich": (13, 15),     # Annual show days 13-15
            "Istanbul": (19, 22)    # Relatives visit days 19-22
        },
        # Inclusion days that must be within the city's stay
        "must_include_days": {
            "Stuttgart": {4, 7}     # Conference day 4 and day 7
        }
    }
    adjacency = build_adjacency()

    # Reykjavik must start the trip at day 1 (from constraints)
    if "Reykjavik" not in cities:
        raise ValueError("Reykjavik must be in the city list due to the workshop constraint.")
    
    # Generate sequences where Reykjavik is first to respect day-1 start.
    remaining_cities = [c for c in cities if c != "Reykjavik"]
    valid_itinerary = None

    for perm in permutations(remaining_cities):
        seq = ["Reykjavik"] + list(perm)
        if not is_flight_path_valid(seq, adjacency):
            continue
        schedule = compute_schedule(seq, durations)

        # Last day must be exactly trip_length
        final_end = schedule[seq[-1]]["end"]
        if final_end != trip_length:
            continue

        # Check constraints
        if not satisfies_constraints(schedule, constraints):
            continue

        # Found a valid sequence
        valid_itinerary = [{"day_range": f"Day {schedule[city]['start']}-{schedule[city]['end']}", "place": city} for city in seq]
        break

    if not valid_itinerary:
        raise RuntimeError("No valid itinerary found that satisfies all constraints and direct flights.")

    result = {"itinerary": valid_itinerary}
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()