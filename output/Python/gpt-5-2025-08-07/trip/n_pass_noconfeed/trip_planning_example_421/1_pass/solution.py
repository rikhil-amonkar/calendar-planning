import json
import itertools

def compute_itinerary():
    # Input variables (trip constraints)
    total_days = 20
    required_stays = {
        "Nice": 5,
        "Krakow": 6,
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2
    }
    # Windows and special constraints
    nice_window = (1, 5)  # Must be in Nice between day 1 and 5 inclusive
    frankfurt_meet_window = (19, 20)  # Must meet friends in Frankfurt between day 19 and day 20
    
    # Direct flights (undirected)
    direct_flights = [
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Lyon", "Dublin"),
        ("Nice", "Lyon"),
    ]
    
    # Build undirected adjacency set
    adj = {}
    for a, b in direct_flights:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    
    cities = list(required_stays.keys())
    start_city = "Nice"
    end_city = "Frankfurt"
    middle_cities = [c for c in cities if c not in {start_city, end_city}]
    
    # Verify overlap feasibility
    sum_durations = sum(required_stays.values())
    required_overlaps = sum_durations - total_days
    transitions_needed = len(cities) - 1  # moving through 5 cities requires 4 legs
    if required_overlaps != transitions_needed:
        # If this occurs, the simple single-visit chain with an overlap on each transition can't satisfy totals
        return {"itinerary": [], "error": "Overlap requirements do not match transitions needed."}
    
    def path_has_direct_flights(order):
        return all(order[i+1] in adj.get(order[i], set()) for i in range(len(order)-1))
    
    def build_schedule(order):
        # We enforce that flight happens on the last day in each city (overlap day),
        # meaning consecutive city intervals overlap by exactly 1 day.
        schedule = []
        current_start = 1
        for city in order:
            dur = required_stays[city]
            end_day = current_start + dur - 1
            schedule.append((city, current_start, end_day))
            current_start = end_day  # Overlap: next city's start equals this end (flight on this day)
        return schedule
    
    def satisfies_constraints(schedule):
        # Extract intervals
        intervals = {city: (start, end) for city, start, end in schedule}
        
        # Nice must be exactly Day 1-5 and for 5 days
        n_start, n_end = intervals["Nice"]
        if not (n_start == nice_window[0] and n_end == nice_window[1] and (n_end - n_start + 1) == required_stays["Nice"]):
            return False
        
        # Frankfurt must cover day 19 and 20, and be exactly 2 days
        f_start, f_end = intervals["Frankfurt"]
        if not (f_start <= frankfurt_meet_window[0] <= f_end and f_start <= frankfurt_meet_window[1] <= f_end):
            return False
        if (f_end - f_start + 1) != required_stays["Frankfurt"]:
            return False
        
        # Entire trip must end on total_days
        if schedule[-1][2] != total_days:
            return False
        
        # All city durations must match exactly
        for city, start, end in schedule:
            if (end - start + 1) != required_stays[city]:
                return False
        
        return True
    
    best_schedule = None
    
    # Try all permutations of middle cities to find a valid path
    for perm in itertools.permutations(middle_cities):
        order = [start_city] + list(perm) + [end_city]
        if not path_has_direct_flights(order):
            continue
        schedule = build_schedule(order)
        if satisfies_constraints(schedule):
            best_schedule = schedule
            break
    
    if not best_schedule:
        return {"itinerary": [], "error": "No feasible itinerary found with given constraints and direct flights."}
    
    # Build output JSON structure
    itinerary = []
    for city, start, end in best_schedule:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = compute_itinerary()
    print(json.dumps(result, ensure_ascii=False))