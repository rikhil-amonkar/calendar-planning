import json
from collections import defaultdict

def find_hamiltonian_paths(start, cities, adjacency):
    # Backtracking to find all Hamiltonian paths starting from 'start'
    n = len(cities)
    results = []
    cities_set = set(cities)

    def backtrack(path, visited):
        if len(path) == n:
            results.append(path[:])
            return
        last = path[-1]
        for neighbor in adjacency[last]:
            if neighbor in cities_set and neighbor not in visited:
                visited.add(neighbor)
                path.append(neighbor)
                backtrack(path, visited)
                path.pop()
                visited.remove(neighbor)

    backtrack([start], {start})
    return results

def schedule_itinerary(order, required_days, total_days):
    # Create overlapping segments: next segment starts on previous end day (flight day overlap)
    segments = []
    current_start = 1
    for city in order:
        end_day = current_start + required_days[city] - 1
        segments.append((current_start, end_day, city))
        current_start = end_day  # overlap next start on the flight day
    final_end = segments[-1][1]
    return segments, final_end

def validate_flights(order, flights_set):
    for a, b in zip(order, order[1:]):
        if (a, b) not in flights_set and (b, a) not in flights_set:
            return False
    return True

def workshop_covered(segments, workshop_city, window_start, window_end):
    # Verify all days in [window_start, window_end] are within workshop_city coverage
    # A day D is within a city's segment if segment_start <= D <= segment_end
    cover = None
    for s, e, city in segments:
        if city == workshop_city:
            cover = (s, e)
            break
    if cover is None:
        return False
    s, e = cover
    return s <= window_start and e >= window_end

def main():
    # Input variables (trip constraints)
    total_days = 11
    city_durations = {
        "Seville": 6,
        "Paris": 2,
        "Krakow": 5
    }
    cities = ["Krakow", "Paris", "Seville"]
    direct_flights = [("Krakow", "Paris"), ("Paris", "Seville")]
    workshop_city = "Krakow"
    workshop_window = (1, 5)  # inclusive

    # Build adjacency
    adjacency = defaultdict(set)
    for a, b in direct_flights:
        adjacency[a].add(b)
        adjacency[b].add(a)
    flights_set = set(direct_flights)

    # Compute required number of flight days (overlaps)
    sum_city_days = sum(city_durations[c] for c in cities)
    required_flights = sum_city_days - total_days
    if required_flights < 0:
        raise ValueError("Infeasible: total_days exceeds sum of city durations.")
    # We aim to use exactly 'required_flights' transitions between cities

    # Generate Hamiltonian paths starting from workshop city (to ensure early presence)
    all_paths = find_hamiltonian_paths(workshop_city, cities, adjacency)

    chosen_segments = None
    chosen_order = None

    for path in all_paths:
        # Validate transitions exist
        if not validate_flights(path, flights_set):
            continue
        # Number of transitions equals len(path)-1
        if len(path) - 1 != required_flights:
            continue
        # Build schedule
        segments, final_end = schedule_itinerary(path, city_durations, total_days)
        # Validate overall total days
        if final_end != total_days:
            continue
        # Validate workshop coverage over the required window
        if not workshop_covered(segments, workshop_city, workshop_window[0], workshop_window[1]):
            continue
        # If all constraints satisfied, choose this itinerary
        chosen_segments = segments
        chosen_order = path
        break

    if chosen_segments is None:
        raise ValueError("No feasible itinerary found under the given constraints.")

    # Prepare JSON output
    itinerary = []
    for s, e, city in chosen_segments:
        itinerary.append({
            "day_range": f"Day {s}-{e}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()