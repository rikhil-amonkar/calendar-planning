#!/usr/bin/env python3
import itertools
import json

# Fixed durations for each city
durations = {
    "Bucharest": 3,
    "Venice": 5,
    "Prague": 4,
    "Frankfurt": 5,
    "Zurich": 5,
    "Florence": 5,
    "Tallinn": 5
}

# The list of all cities
cities = list(durations.keys())

# Flight connections.
# Each flight is a tuple: (cityA, cityB, directed)
# For non‐directed flights, the order does not matter.
# For the “from Zurich to Florence” flight, directed=True means the flight is only allowed in that direction.
flights = [
    ("Prague", "Tallinn", False),
    ("Prague", "Zurich", False),
    ("Florence", "Prague", False),
    ("Frankfurt", "Bucharest", False),
    ("Frankfurt", "Venice", False),
    ("Prague", "Bucharest", False),
    ("Bucharest", "Zurich", False),
    ("Tallinn", "Frankfurt", False),
    ("Zurich", "Florence", True),   # directed: only allowed from Zurich to Florence
    ("Frankfurt", "Zurich", False),
    ("Zurich", "Venice", False),
    ("Florence", "Frankfurt", False),
    ("Prague", "Frankfurt", False),
    ("Tallinn", "Zurich", False)
]

def flight_exists(city_from, city_to):
    """
    Returns True if there is a direct flight from city_from to city_to based on flights list.
    For undirected flights, the connection is available both ways.
    For directed flights, the order must match.
    """
    for (a, b, directed) in flights:
        if directed:
            # For a directed flight, must match order.
            if city_from == a and city_to == b:
                return True
        else:
            if (city_from == a and city_to == b) or (city_from == b and city_to == a):
                return True
    return False

def compute_itinerary_info(order):
    """
    Given an ordering of cities, compute the start and end day for each city.
    According to the rule: if you fly on day X from city A to city B then day X counts for both A and B.
    Thus, the start day of the first city is 1.
    For i > 0: start_day[i] = start_day[i-1] + (duration(previous) - 1)
    Also compute end_day[i] = start_day[i] + durations[city] - 1.
    Return list of tuples (city, start_day, end_day)
    """
    itinerary = []
    day = 1
    for i, city in enumerate(order):
        start_day = day
        end_day = start_day + durations[city] - 1
        itinerary.append((city, start_day, end_day))
        # Next city starts on the same day as the previous city’s end day (flight day is overlapped)
        day = end_day  # because the flight day is the end_day (overlap)
        # Then add one less day because the day is counted for both cities.
        # In effect, the overall trip length = sum(duration) - (number of flights)
    return itinerary

def check_total_days(itinerary):
    # Total trip days = (end_day of last city) because days start at 1.
    last_city = itinerary[-1]
    return last_city[2] == 26  # Must be exactly 26 days

def check_flight_connectivity(order):
    # Check that for each consecutive pair of cities there is a direct flight.
    for i in range(len(order) - 1):
        if not flight_exists(order[i], order[i+1]):
            return False
    return True

def check_event_constraints(itinerary):
    # For each city, check if any event constraint applies:
    # Frankfurt: The annual show runs from day 12 to day 16;
    # the 5-day stay in Frankfurt must cover that interval entirely.
    # So if Frankfurt's schedule is [s, s+4], we require s <= 12 and (s+4) >= 16.
    # Tallinn: Friend meeting in Tallinn must occur between day 8 and day 12.
    # We require that Tallinn's interval [s, s+duration-1] overlaps [8,12].
    # Venice: Wedding in Venice must be attended between day 22 and day 26 (overlap required).
    for city, start_day, end_day in itinerary:
        if city == "Frankfurt":
            if not (start_day <= 12 and end_day >= 16):
                return False
        if city == "Tallinn":
            # Overlap: latest start <= 12 and earliest end >= 8
            if not (start_day <= 12 and end_day >= 8):
                return False
        if city == "Venice":
            if not (start_day <= 26 and end_day >= 22):
                return False
    return True

def main():
    valid_itinerary = None
    # Try all permutations of the 7 cities.
    for order in itertools.permutations(cities):
        # First, check flight connectivity for the complete order.
        if not check_flight_connectivity(order):
            continue

        # Compute itinerary start/end days based on the rule.
        itinerary_info = compute_itinerary_info(order)
        # Check total trip length is 26 days.
        if not check_total_days(itinerary_info):
            continue

        # Check event constraints.
        if not check_event_constraints(itinerary_info):
            continue

        # If all constraints satisfied, choose this itinerary.
        valid_itinerary = itinerary_info
        break

    if valid_itinerary is None:
        # If no valid itinerary is found, output a JSON with an empty itinerary.
        result = {"itinerary": "No valid itinerary found with the given constraints."}
    else:
        # Build the JSON structure.
        itinerary_list = []
        for (city, s, e) in valid_itinerary:
            day_range = f"Day {s}-{e}"
            itinerary_list.append({"day_range": day_range, "place": city})
        result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()