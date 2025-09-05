import itertools
import json

def main():
    total_days = 21

    # Define the cities with required durations
    durations = {
        "Manchester": 3,
        "Istanbul": 7,
        "Venice": 7,
        "Krakow": 6,
        "Lyon": 2
    }
    
    # Define the direct flight connections (bidirectional)
    flight_graph = {
        "Manchester": {"Venice", "Istanbul", "Krakow"},
        "Venice": {"Manchester", "Istanbul", "Lyon"},
        "Istanbul": {"Manchester", "Venice", "Krakow", "Lyon"},
        "Krakow": {"Manchester", "Istanbul"},
        "Lyon": {"Venice", "Istanbul"}
    }
    
    # Specific constraints:
    # Wedding in Manchester must be attended between day 1 and day 3.
    wedding_city = "Manchester"
    wedding_time_window = (1, 3)  # inclusive window
    
    # Workshop in Venice must be attended between day 3 and day 9.
    workshop_city = "Venice"
    workshop_time_window = (3, 9)  # inclusive window
    
    # To satisfy the wedding timing, we fix Manchester as the starting city.
    start_city = "Manchester"
    all_cities = list(durations.keys())
    remaining_cities = [city for city in all_cities if city != start_city]
    
    valid_itinerary = None

    # We try all permutations of the remaining cities to see which ordering works with flight connectivity and constraints.
    for perm in itertools.permutations(remaining_cities):
        order = [start_city] + list(perm)
        
        # Check that each flight between consecutive cities is direct.
        route_ok = True
        for i in range(len(order) - 1):
            c1, c2 = order[i], order[i+1]
            if c2 not in flight_graph[c1] and c1 not in flight_graph[c2]:
                route_ok = False
                break
        if not route_ok:
            continue
            
        # Construct the itinerary schedule using the overlapping flight days rule.
        # If you fly on day X from city A to B, then day X counts for both A and B.
        current_day = 1
        itinerary = []
        schedule = {}  # To store arrival and departure days for each city.
        for idx, city in enumerate(order):
            arrival = current_day
            departure = arrival + durations[city] - 1
            schedule[city] = (arrival, departure)
            itinerary.append({"day_range": f"Day {arrival}-{departure}", "place": city})
            # For all but the last city, the next city's arrival is the same day as the departure (flight day overlap).
            if idx < len(order) - 1:
                current_day = departure
        
        # Ensure the final departure day equals the total trip days.
        final_city = order[-1]
        if schedule[final_city][1] != total_days:
            continue
        
        # Check the workshop constraint for Venice: the Venice visit must overlap with days 3-9.
        if workshop_city in schedule:
            arrival_v, departure_v = schedule[workshop_city]
            # Overlap exists if Venice's period is not completely before day 3 or completely after day 9.
            if arrival_v > workshop_time_window[1] or departure_v < workshop_time_window[0]:
                continue
        else:
            continue  # Venice must be visited.
            
        # Check the wedding constraint for Manchester: it must include a day between day 1 and day 3.
        if wedding_city in schedule:
            arrival_w, departure_w = schedule[wedding_city]
            if departure_w < wedding_time_window[0] or arrival_w > wedding_time_window[1]:
                continue
        else:
            continue  # Manchester must be visited.
        
        # If all constraints are met, we select this itinerary.
        valid_itinerary = itinerary
        break

    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": valid_itinerary}
    
    # Output the itinerary as a JSON-formatted dictionary.
    print(json.dumps(result))

if __name__ == "__main__":
    main()