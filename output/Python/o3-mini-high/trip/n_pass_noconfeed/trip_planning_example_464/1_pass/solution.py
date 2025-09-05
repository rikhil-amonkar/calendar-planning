import itertools
import json

def interval_intersects(a, b, c, d):
    # Returns True if interval [a, b] and [c, d] intersect
    return not (b < c or a > d)

def compute_itinerary(order, durations):
    itinerary = []
    day = 1
    for city in order:
        start = day
        end = start + durations[city] - 1
        itinerary.append((city, start, end))
        # Next city starts on the same day as the flight day (overlap)
        day = end  
    return itinerary

def main():
    total_days = 18
    # Define durations for each city (in days)
    durations = {
        "Krakow": 5,
        "Frankfurt": 4,
        "Oslo": 3,
        "Dubrovnik": 5,
        "Naples": 5
    }
    
    # Define allowed direct flights (bidirectional)
    flights = {
        frozenset(["Dubrovnik", "Oslo"]),
        frozenset(["Frankfurt", "Krakow"]),
        frozenset(["Frankfurt", "Oslo"]),
        frozenset(["Dubrovnik", "Frankfurt"]),
        frozenset(["Krakow", "Oslo"]),
        frozenset(["Naples", "Oslo"]),
        frozenset(["Naples", "Dubrovnik"]),
        frozenset(["Naples", "Frankfurt"])
    }
    
    # Special timing constraints:
    # - Meet friends in Dubrovnik between day 5 and 9.
    dubrovnik_time_window = (5, 9)
    # - Visit relatives in Oslo between day 16 and 18.
    oslo_time_window = (16, 18)
    
    cities = list(durations.keys())
    valid_itinerary = None
    
    # Iterate over all possible orders of the five cities
    for order in itertools.permutations(cities):
        # Check if each consecutive city pair has a direct flight
        valid_route = True
        for i in range(1, len(order)):
            if frozenset([order[i-1], order[i]]) not in flights:
                valid_route = False
                break
        if not valid_route:
            continue
        
        # Compute the day ranges for each city in the itinerary
        itinerary = compute_itinerary(order, durations)
        
        # Verify that the final day equals the total trip days
        if itinerary[-1][2] != total_days:
            continue
        
        # Check special timing constraints in each relevant city segment
        meets_constraints = True
        for city, start, end in itinerary:
            if city == "Dubrovnik":
                if not interval_intersects(start, end, dubrovnik_time_window[0], dubrovnik_time_window[1]):
                    meets_constraints = False
                    break
            if city == "Oslo":
                if not interval_intersects(start, end, oslo_time_window[0], oslo_time_window[1]):
                    meets_constraints = False
                    break
        if not meets_constraints:
            continue
        
        # Found a valid itinerary that satisfies all constraints!
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