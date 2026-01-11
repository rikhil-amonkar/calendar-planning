import json
from itertools import permutations

# Cities and required days
cities = {
    'Salzburg': 2,
    'Venice': 5,
    'Bucharest': 4,
    'Brussels': 2,
    'Hamburg': 4,
    'Copenhagen': 4,
    'Nice': 3,
    'Zurich': 5,
    'Naples': 4
}

# Direct flights as adjacency list
flights = {
    'Zurich': ['Brussels', 'Nice', 'Naples', 'Copenhagen', 'Venice', 'Hamburg', 'Bucharest'],
    'Brussels': ['Zurich', 'Venice', 'Bucharest', 'Hamburg', 'Nice', 'Copenhagen', 'Naples'],
    'Venice': ['Brussels', 'Naples', 'Copenhagen', 'Zurich', 'Nice', 'Hamburg'],
    'Nice': ['Zurich', 'Hamburg', 'Brussels', 'Naples', 'Copenhagen', 'Venice'],
    'Hamburg': ['Nice', 'Bucharest', 'Brussels', 'Copenhagen', 'Venice', 'Zurich', 'Salzburg'],
    'Bucharest': ['Copenhagen', 'Hamburg', 'Brussels', 'Naples', 'Zurich'],
    'Copenhagen': ['Bucharest', 'Zurich', 'Venice', 'Hamburg', 'Nice', 'Brussels', 'Naples'],
    'Naples': ['Zurich', 'Venice', 'Bucharest', 'Copenhagen', 'Nice', 'Brussels'],
    'Salzburg': ['Hamburg']
}

# Add reverse edges
for city in list(flights.keys()):
    for dest in flights[city]:
        if city not in flights[dest]:
            flights[dest].append(city)

# Date constraints: each is (city, start_day, end_day) inclusive
constraints = [
    ('Brussels', 21, 22),
    ('Copenhagen', 18, 21),
    ('Nice', 9, 11),
    ('Naples', 22, 25)
]

def satisfies_constraints(itinerary):
    # itinerary: list of (city, start_day, end_day)
    for city, req_start, req_end in constraints:
        found = False
        for visit_city, start, end in itinerary:
            if visit_city == city:
                # Check if any day of visit overlaps with required interval
                if not (end < req_start or start > req_end):
                    # Overlap exists, check if whole required interval is inside visit
                    if start <= req_start and end >= req_end:
                        found = True
                        break
        if not found:
            return False
    return True

def total_days(itinerary):
    # Sum of days in each city
    total = 0
    for _, start, end in itinerary:
        total += (end - start + 1)
    return total

def find_itinerary():
    city_names = list(cities.keys())
    # Try permutations of cities (prune early for feasibility)
    for perm in permutations(city_names):
        # Build itinerary
        day = 1
        itinerary = []
        possible = True
        for i, city in enumerate(perm):
            stay_len = cities[city]
            if i == 0:
                start_day = day
                end_day = start_day + stay_len - 1
            else:
                # Travel day is the last day of previous city and first day of this city
                # So this city starts on the same day previous ended
                start_day = day
                end_day = start_day + stay_len - 1
            itinerary.append((city, start_day, end_day))
            day = end_day  # Next city starts after this one ends? Wait, travel day is shared, so next city starts on same day this ends.
            # Actually: If we are in city A on day X (last day), we fly to city B on day X, so B's first day is day X.
            # So B's start_day = A's end_day.
            # Then B's end_day = start_day + stay_len - 1.
            # Then next city's start_day = B's end_day.
            # So day = end_day (no +1).
            # But careful: This means total calendar days = last end_day.
            # Let's implement correctly:
            # For first city: start_day=1, end_day=1+stay-1.
            # For next city: start_day = prev_end_day (because travel day shared), end_day = start_day + stay - 1.
            # So we update day = end_day for next iteration.
            # This is already done above.
            
            # Check adjacency
            if i > 0:
                prev_city = perm[i-1]
                if city not in flights[prev_city]:
                    possible = False
                    break
        if not possible:
            continue
        
        # Check total days = 25
        if itinerary[-1][2] != 25:
            continue
        
        # Check constraints
        if satisfies_constraints(itinerary):
            return itinerary
    return None

def format_itinerary(itinerary):
    result = []
    for city, start, end in itinerary:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        result.append({"day_range": day_range, "place": city})
    return result

def main():
    itinerary = find_itinerary()
    if itinerary is None:
        print('{"error": "No valid itinerary found"}')
        return
    
    formatted = format_itinerary(itinerary)
    output = {"itinerary": formatted}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()