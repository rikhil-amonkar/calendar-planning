#!/usr/bin/env python3
import json
import itertools

def compute_itinerary(route, durations):
    itinerary = []
    current_day = 1
    for city in route:
        start_day = current_day
        end_day = start_day + durations[city] - 1
        itinerary.append((city, start_day, end_day))
        # The flight day (end_day) counts for both cities, so next city starts on the same day.
        current_day = end_day
    return itinerary

def check_event_constraints(itinerary):
    # Check Porto workshop: must be in Porto on a day between 1 and 3.
    for city, start, end in itinerary:
        if city == "Porto":
            # Workshop must occur between day 1 and day 3
            if end < 1 or start > 3:
                return False
    # Check Warsaw wedding: must attend wedding in Warsaw between day 13 and day 15.
    for city, start, end in itinerary:
        if city == "Warsaw":
            # There must be an overlap between Warsaw's visit and [13,15]
            if start > 15 or end < 13:
                return False
    # Check Vienna relatives: must visit relatives in Vienna between day 19 and day 20.
    for city, start, end in itinerary:
        if city == "Vienna":
            if start > 20 or end < 19:
                return False
    return True

def main():
    total_days = 20
    durations = {
        "Paris": 5,
        "Florence": 3,
        "Vienna": 2,
        "Porto": 3,
        "Munich": 5,
        "Nice": 5,
        "Warsaw": 3
    }
    
    # Define direct flight connections (assumed bidirectional)
    flights = [
        ("Florence", "Vienna"),
        ("Paris", "Warsaw"),
        ("Munich", "Vienna"),
        ("Porto", "Vienna"),
        ("Warsaw", "Vienna"),
        ("Florence", "Munich"),  # given as "from Florence to Munich"
        ("Munich", "Warsaw"),
        ("Munich", "Nice"),
        ("Paris", "Florence"),
        ("Warsaw", "Nice"),
        ("Porto", "Munich"),
        ("Porto", "Nice"),
        ("Paris", "Vienna"),
        ("Nice", "Vienna"),
        ("Porto", "Paris"),
        ("Paris", "Nice"),
        ("Paris", "Munich"),
        ("Porto", "Warsaw")
    ]
    available_flights = set(frozenset((a, b)) for a, b in flights)
    
    # List of cities to visit
    cities = ["Porto", "Paris", "Florence", "Vienna", "Munich", "Nice", "Warsaw"]
    # To meet workshop and relatives constraints, we fix Porto as the starting city and Vienna as the final city.
    middle_cities = [city for city in cities if city not in ["Porto", "Vienna"]]
    
    valid_itinerary = None
    # Try all permutations of the middle cities.
    for perm in itertools.permutations(middle_cities):
        route = ["Porto"] + list(perm) + ["Vienna"]
        # Check that every consecutive flight is available.
        valid_route = True
        for i in range(len(route) - 1):
            if frozenset((route[i], route[i+1])) not in available_flights:
                valid_route = False
                break
        if not valid_route:
            continue
        
        # Compute itinerary timeline based on overlapping flight days.
        itinerary = compute_itinerary(route, durations)
        # Check that the final day matches the total trip days.
        if itinerary[-1][2] != total_days:
            continue
        # Check event constraints (workshop, wedding, relatives)
        if not check_event_constraints(itinerary):
            continue
        
        valid_itinerary = itinerary
        break

    if valid_itinerary is None:
        output = {"itinerary": []}
    else:
        itinerary_list = []
        for city, start, end in valid_itinerary:
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
        output = {"itinerary": itinerary_list}
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()