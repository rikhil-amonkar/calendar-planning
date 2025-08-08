#!/usr/bin/env python3
import json
import itertools

def is_direct_connection(city_a, city_b, symmetric_edges, directed_edges):
    # Check symmetric connection
    if frozenset([city_a, city_b]) in symmetric_edges:
        return True
    # Check directed connection (only in the given order)
    if (city_a, city_b) in directed_edges:
        return True
    return False

def compute_schedule(itinerary, durations, total_days):
    schedule = []  # list of tuples: (city, start_day, end_day)
    current_day = 1
    for city in itinerary:
        d = durations[city]
        start_day = current_day
        end_day = start_day + d - 1
        schedule.append((city, start_day, end_day))
        # The flight day is the same as the end day of the current city.
        current_day = end_day
    if schedule and schedule[-1][2] == total_days:
        return schedule
    else:
        return None

def schedule_satisfies_events(schedule, event_constraints):
    # For each city with an event constraint, check
    # that the city's scheduled interval [start, end] overlaps the required window.
    # Overlap condition: city_start <= event_window_end and city_end >= event_window_start.
    for city, event_window in event_constraints.items():
        # Find the scheduled interval for 'city'
        found = False
        for entry in schedule:
            scheduled_city, start_day, end_day = entry
            if scheduled_city == city:
                found = True
                window_start, window_end = event_window
                if not (start_day <= window_end and end_day >= window_start):
                    return False
                break
        if not found:
            # If the city with an event is not in our itinerary the constraint isn't met.
            return False
    return True

def main():
    # Trip parameters / input variables:
    total_days = 14
    # Durations needed in each city (each flight day counts for both cities)
    durations = {
        "Helsinki": 2,  # Must attend workshop between day1 and day2.
        "Warsaw": 3,    # Visit relatives between day9 and day11.
        "Madrid": 4,
        "Split": 4,
        "Reykjavik": 2, # Meet friend between day8 and day9.
        "Budapest": 4
    }
    
    # Event constraints: city -> (required window start, required window end)
    event_constraints = {
        "Helsinki": (1, 2),   # Workshop in Helsinki between day1 and day2.
        "Warsaw": (9, 11),    # Visit relatives in Warsaw between day9 and day11.
        "Reykjavik": (8, 9)   # Meet friend in Reykjavik between day8 and day9.
    }
    
    # Direct flight connections are given.
    # Most flights are bidirectional (symmetric) except the explicitly listed "from Reykjavik to Madrid".
    symmetric_edges = {
        frozenset(["Helsinki", "Reykjavik"]),
        frozenset(["Budapest", "Warsaw"]),
        frozenset(["Madrid", "Split"]),
        frozenset(["Helsinki", "Split"]),
        frozenset(["Helsinki", "Madrid"]),
        frozenset(["Helsinki", "Budapest"]),
        frozenset(["Reykjavik", "Warsaw"]),
        frozenset(["Helsinki", "Warsaw"]),
        frozenset(["Madrid", "Budapest"]),
        frozenset(["Budapest", "Reykjavik"]),
        frozenset(["Madrid", "Warsaw"]),
        frozenset(["Warsaw", "Split"])
    }
    directed_edges = {
        ("Reykjavik", "Madrid")
    }
    
    # List of cities. Helsinki must be the starting city because of the workshop constraint.
    all_cities = list(durations.keys())
    start_city = "Helsinki"
    remaining_cities = [city for city in all_cities if city != start_city]
    
    valid_itinerary = None
    valid_schedule = None
    
    # Permute remaining cities and prepend Helsinki.
    for perm in itertools.permutations(remaining_cities):
        itinerary = [start_city] + list(perm)
        
        # Check direct flight connection for each consecutive pair.
        valid_connection = True
        for i in range(len(itinerary) - 1):
            if not is_direct_connection(itinerary[i], itinerary[i+1], symmetric_edges, directed_edges):
                valid_connection = False
                break
        if not valid_connection:
            continue
        
        # Compute day schedule given the durations and overlapping flight days.
        schedule = compute_schedule(itinerary, durations, total_days)
        if schedule is None:
            continue
        
        # Check event constraints (the required day windows).
        if not schedule_satisfies_events(schedule, event_constraints):
            continue
        
        # If all conditions are met, we have found a valid itinerary.
        valid_itinerary = itinerary
        valid_schedule = schedule
        break
    
    # Build the JSON output structure if a valid itinerary is found.
    output = {}
    itinerary_output = []
    if valid_schedule:
        for city, start_day, end_day in valid_schedule:
            itinerary_output.append({
                "day_range": "Day {}-{}".format(start_day, end_day),
                "place": city
            })
        output["itinerary"] = itinerary_output
    else:
        output["itinerary"] = []
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()