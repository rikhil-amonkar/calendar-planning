#!/usr/bin/env python3
import itertools
import json

def compute_itinerary():
    # Trip constraints and input variables
    total_days = 16
    required_durations = {
        "Mykonos": 4,
        "London": 2,
        "Copenhagen": 3,
        "Oslo": 5,
        "Tallinn": 4,
        "Nice": 3
    }
    # Flight connections (bidirectional)
    flight_graph = {
        "London": {"Copenhagen", "Nice", "Oslo", "Mykonos"},
        "Copenhagen": {"London", "Tallinn", "Nice", "Oslo"},
        "Tallinn": {"Copenhagen", "Oslo"},
        "Oslo": {"Tallinn", "Nice", "London", "Copenhagen"},
        "Mykonos": {"London", "Nice"},
        "Nice": {"Oslo", "London", "Mykonos", "Copenhagen"}
    }
    
    # Conference constraints: Nice must be visited on day 14 and day 16.
    # Friend meeting: In Oslo, some day between day 10 and day 14.
    
    # We know the overall required sum of durations is:
    # sum(required_durations.values()) = 21, but with 5 overlapping flight days that gives 16 total days.
    # Also, since Nice must include day 16 (the final day of the trip) and day 14,
    # we force Nice to be the last destination.
    
    cities = ["Mykonos", "London", "Copenhagen", "Oslo", "Tallinn", "Nice"]
    non_nice_cities = [city for city in cities if city != "Nice"]
    
    # Function to compute itinerary day ranges given an ordered list of cities.
    # According to the rule: the first city starts on day 1.
    # For each subsequent flight day, the flight day is the overlap (i.e. start_day[i] = end_day[i-1])
    # and end_day[i] = start_day[i] + duration - 1.
    def compute_day_ranges(order):
        day_ranges = []
        start_day = 1
        for city in order:
            duration = required_durations[city]
            end_day = start_day + duration - 1
            day_ranges.append((start_day, end_day))
            # Next city's start is the same as this city's end (overlap flight day)
            start_day = end_day
        return day_ranges

    # Check if two intervals [a,b] and [c,d] intersect.
    def intervals_intersect(a, b, c, d):
        return a <= d and c <= b

    valid_itinerary = None
    
    # Iterate over all orders with Nice as the final city.
    for perm in itertools.permutations(non_nice_cities):
        itinerary_order = list(perm) + ["Nice"]
        
        # Check flight connectivity for each transition.
        valid_route = True
        for i in range(len(itinerary_order) - 1):
            current_city = itinerary_order[i]
            next_city = itinerary_order[i+1]
            if next_city not in flight_graph[current_city]:
                valid_route = False
                break
        if not valid_route:
            continue
        
        # Compute day ranges for each segment.
        day_ranges = compute_day_ranges(itinerary_order)
        # The overall final day must equal total_days.
        if day_ranges[-1][1] != total_days:
            continue
        
        # Check conference constraints for Nice.
        # Since Nice is the final city, its day range must cover day 14 and day 16.
        nice_index = itinerary_order.index("Nice")
        nice_start, nice_end = day_ranges[nice_index]
        if not (nice_start <= 14 <= nice_end and nice_start <= 16 <= nice_end):
            continue
        
        # Check friend meeting in Oslo: Oslo's day range must include at least one day between 10 and 14.
        if "Oslo" in itinerary_order:
            oslo_index = itinerary_order.index("Oslo")
            oslo_start, oslo_end = day_ranges[oslo_index]
            # Check intersection with [10, 14]
            if not intervals_intersect(oslo_start, oslo_end, 10, 14):
                continue
        else:
            continue  # Oslo must be visited
        
        # If all constraints are met, we use this itinerary.
        valid_itinerary = {"order": itinerary_order, "day_ranges": day_ranges}
        break

    if valid_itinerary is None:
        return None

    # Build the output JSON structure.
    itinerary_list = []
    for city, (start, end) in zip(valid_itinerary["order"], valid_itinerary["day_ranges"]):
        itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city})
    
    output = {"itinerary": itinerary_list}
    return output

def main():
    plan = compute_itinerary()
    if plan is None:
        print(json.dumps({"error": "No valid itinerary found"}))
    else:
        print(json.dumps(plan))
        
if __name__ == '__main__':
    main()