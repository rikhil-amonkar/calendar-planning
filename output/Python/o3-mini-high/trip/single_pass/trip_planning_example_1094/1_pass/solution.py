#!/usr/bin/env python3
import json
import itertools

def build_allowed_flights():
    # Allowed flights as provided.
    # For most pairs we assume bidirectional except for the "from Riga to Hamburg" route.
    directed = {
        ("Hamburg", "Stockholm"),
        ("Vienna", "Stockholm"),
        ("Paris", "Edinburgh"),
        ("Riga", "Barcelona"),
        ("Paris", "Riga"),
        ("Krakow", "Barcelona"),
        ("Edinburgh", "Stockholm"),
        ("Paris", "Krakow"),
        ("Krakow", "Stockholm"),
        ("Riga", "Edinburgh"),
        ("Barcelona", "Stockholm"),
        ("Paris", "Stockholm"),
        ("Krakow", "Edinburgh"),
        ("Vienna", "Hamburg"),
        ("Paris", "Hamburg"),
        ("Riga", "Stockholm"),
        ("Hamburg", "Barcelona"),
        ("Vienna", "Barcelona"),
        ("Krakow", "Vienna"),
        ("Barcelona", "Edinburgh"),
        ("Paris", "Barcelona"),
        ("Hamburg", "Edinburgh"),
        ("Paris", "Vienna"),
        ("Vienna", "Riga"),
        # The following is directional: only allowed from Riga to Hamburg.
        ("Riga", "Hamburg")
    }
    # For all flights except the special directional one ("Riga","Hamburg"), add the reverse direction.
    allowed = set(directed)
    for (a, b) in list(directed):
        if (a, b) == ("Riga", "Hamburg"):
            # Do not add reverse for the directional flight.
            continue
        allowed.add((b, a))
    return allowed

def is_valid_flight(city_from, city_to, allowed_routes):
    return (city_from, city_to) in allowed_routes

def compute_start_days(itinerary, durations):
    # Using the rule: first city starts on day 1.
    # If a city with duration d is traveled from, then the next city starts on the same day as the previous city ends.
    # Formally: start[0] = 1, and for i>=1: start[i] = start[i-1] + durations[itinerary[i-1]] - 1.
    start_days = []
    current_start = 1
    for city in itinerary:
        start_days.append(current_start)
        current_start = current_start + durations[city] - 1
    return start_days

def check_constraints(itinerary, start_days, durations, allowed_routes):
    n = len(itinerary)
    # 1. Check flight connectivity between consecutive cities.
    for i in range(n - 1):
        if not is_valid_flight(itinerary[i], itinerary[i+1], allowed_routes):
            return False

    # 2. Check overall trip length: last city end day must be 16.
    final_end = start_days[-1] + durations[itinerary[-1]] - 1
    if final_end != 16:
        return False

    # 3. Special event constraints:
    #    - Wedding in Paris between day 1 and day 2.
    #      Paris should be visited on day1-2. We force Paris as first so that is ensured.
    if itinerary[0] != "Paris":
        return False
    paris_start = start_days[0]
    paris_end = paris_start + durations["Paris"] - 1
    if not (1 >= paris_start and 2 <= paris_end or (paris_start <= 1 and paris_end >= 2) or (1 <= paris_start <= 2)):
        # Actually, since Paris is forced as first and duration is 2, it always covers days 1-2.
        return False

    #    - Hamburg conference should be on day 10 and day 11.
    #      If Hamburg is in the itinerary, its start day must be 10.
    if "Hamburg" in itinerary:
        idx = itinerary.index("Hamburg")
        if start_days[idx] != 10:
            return False
        # Also, Hamburg's range: day 10 to 10+2-1 = 10-11.
        hamburg_end = start_days[idx] + durations["Hamburg"] - 1
        if hamburg_end < 11:
            return False

    #    - Friend meeting in Edinburgh between day 12 and day 15.
    #      Edinburgh's visit must overlap with [12,15]. (Edinburgh has duration 4.)
    if "Edinburgh" in itinerary:
        idx = itinerary.index("Edinburgh")
        s = start_days[idx]
        e = s + durations["Edinburgh"] - 1
        # Check if the interval [s,e] overlaps with [12,15]
        if e < 12 or s > 15:
            return False

    #    - Relatives in Stockholm between day 15 and day 16.
    #      We force Stockholm to be the last city so that its start day must be 15.
    if itinerary[-1] != "Stockholm":
        return False
    if start_days[-1] != 15:
        return False

    return True

def main():
    # Define cities and durations:
    durations = {
        "Vienna": 4,
        "Barcelona": 2,
        "Edinburgh": 4,
        "Krakow": 3,
        "Riga": 4,
        "Hamburg": 2,
        "Paris": 2,
        "Stockholm": 2
    }
    
    # The list of cities we must visit.
    cities = list(durations.keys())
    # We want Paris to be visited at the very start (for the wedding) and Stockholm at the very end (for relatives).
    fixed_first = "Paris"
    fixed_last = "Stockholm"
    
    # The remaining cities to permute:
    remaining = [city for city in cities if city not in (fixed_first, fixed_last)]
    
    allowed_routes = build_allowed_flights()
    
    valid_itinerary = None
    valid_start_days = None
    
    # Generate all permutations of the remaining 6 cities.
    for perm in itertools.permutations(remaining):
        candidate = [fixed_first] + list(perm) + [fixed_last]
        start_days = compute_start_days(candidate, durations)
        if check_constraints(candidate, start_days, durations, allowed_routes):
            valid_itinerary = candidate
            valid_start_days = start_days
            break

    if not valid_itinerary:
        result = {"itinerary": []}
    else:
        # Build itinerary with day ranges.
        itinerary_list = []
        for city, start in zip(valid_itinerary, valid_start_days):
            end = start + durations[city] - 1
            day_range = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_list}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()