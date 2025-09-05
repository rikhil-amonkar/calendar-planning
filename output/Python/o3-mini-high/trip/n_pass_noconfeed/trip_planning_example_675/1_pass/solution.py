import itertools
import json

# Define the cities with required durations (in days)
durations = {
    "Dubrovnik": 4,
    "Split": 3,
    "Milan": 3,
    "Porto": 4,
    "Krakow": 2,
    "Munich": 5
}

# List of all cities
cities = list(durations.keys())

# Define the allowed direct flight connections (bidirectional)
allowed_flights = {
    frozenset(["Munich", "Porto"]),
    frozenset(["Split", "Milan"]),
    frozenset(["Milan", "Porto"]),
    frozenset(["Munich", "Krakow"]),
    frozenset(["Munich", "Milan"]),
    frozenset(["Dubrovnik", "Munich"]),
    frozenset(["Krakow", "Split"]),
    frozenset(["Krakow", "Milan"]),
    frozenset(["Munich", "Split"])
}

def has_direct_flight(city_a, city_b):
    return frozenset([city_a, city_b]) in allowed_flights

# Check event/wedding/show constraints:
# - In Munich, you must attend the annual show from day 4 to day 8, so your Munich visit must cover days 4 through 8.
# - In Milan, you attend a wedding between day 11 and day 13; so your Milan visit must intersect the window [11, 13].
# - In Krakow, you want to meet your friends between day 8 and day 9; so your Krakow visit must include at least one day in [8, 9].

def check_event_constraints(itinerary):
    for city, start, end in itinerary:
        if city == "Munich":
            # Munich visit must cover days 4 through 8.
            if not (start <= 4 and end >= 8):
                return False
        if city == "Milan":
            # Wedding in Milan between day 11 and 13; require overlap with [11, 13]
            if not (start <= 13 and end >= 11):
                return False
        if city == "Krakow":
            # Meeting friends in Krakow between day 8 and 9; require at least one of those days falls in the interval.
            if not ((start <= 8 <= end) or (start <= 9 <= end)):
                return False
    return True

# Given an ordering of cities, compute the itinerary day ranges.
# If you fly from city A to city B on day X then that day counts for both cities.
def compute_itinerary(order):
    itinerary = []
    current_day = 1
    for city in order:
        d = durations[city]
        start_day = current_day
        end_day = start_day + d - 1
        itinerary.append((city, start_day, end_day))
        # Next city's start day is the same as the current end day (flight day overlap)
        current_day = end_day
    return itinerary

# The total trip length must be 16 days.
def total_trip_days(itinerary):
    # Last city's end day is the total days
    return itinerary[-1][2]

# Iterate over all possible orders and pick one that satisfies all constraints.
def find_optimal_itinerary():
    for order in itertools.permutations(cities):
        # Check direct flight connectivity between consecutive cities.
        valid_flights = True
        for i in range(len(order) - 1):
            if not has_direct_flight(order[i], order[i+1]):
                valid_flights = False
                break
        if not valid_flights:
            continue
        
        itinerary = compute_itinerary(order)
        
        # The total trip must be exactly 16 days.
        if total_trip_days(itinerary) != 16:
            continue
        
        # Check event constraints (Munich show, Milan wedding, Krakow meeting)
        if not check_event_constraints(itinerary):
            continue
        
        # We found a valid itinerary; return it.
        return itinerary
    return None

def main():
    itinerary_data = find_optimal_itinerary()
    if itinerary_data is None:
        result = {"itinerary": []}
    else:
        # Format the itinerary as required.
        itinerary_list = []
        for city, start, end in itinerary_data:
            day_range = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_list}
        
    # Output the result as JSON.
    print(json.dumps(result))

if __name__ == "__main__":
    main()