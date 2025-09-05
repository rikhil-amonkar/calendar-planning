import json
from itertools import permutations

def main():
    # Input variables: total days, required days in each city, and flight connections.
    total_days = 17
    required_days = {
        "Riga": 7,
        "Budapest": 7,
        "Paris": 4,
        "Warsaw": 2
    }
    # Define the bidirectional flight graph (only direct flights allowed)
    flight_graph = {
        "Warsaw": ["Budapest", "Riga", "Paris"],
        "Budapest": ["Warsaw", "Paris"],
        "Paris": ["Budapest", "Warsaw", "Riga"],
        "Riga": ["Warsaw", "Paris"]
    }
    
    # Special event constraints:
    # 1. Annual show in Warsaw from Day 1 to Day 2 ==> Must start in Warsaw.
    # 2. Wedding in Riga must occur during the stay between Day 11 and Day 17.
    wedding_window = (11, 17)
    
    # The cities to visit. We have four cities.
    cities = list(required_days.keys())  # This gives ['Riga', 'Budapest', 'Paris', 'Warsaw'] (order not fixed)
    # Constrain the itinerary: it must start in Warsaw and end in Riga.
    start_city = "Warsaw"
    end_city = "Riga"
    middle_cities = [city for city in cities if city not in (start_city, end_city)]
    
    valid_itinerary = None

    # Try all orders (permutations) of the middle cities.
    for perm in permutations(middle_cities):
        itinerary_order = [start_city] + list(perm) + [end_city]
        
        # Check if every consecutive flight is available.
        valid_route = True
        for i in range(len(itinerary_order) - 1):
            current_city = itinerary_order[i]
            next_city = itinerary_order[i+1]
            if next_city not in flight_graph.get(current_city, []):
                valid_route = False
                break
        if not valid_route:
            continue

        # Compute the day schedule using overlapping flight days.
        # When flying from city A to B on day X, that day counts for both cities.
        schedule = []
        current_day = 1
        valid_schedule = True
        for index, city in enumerate(itinerary_order):
            start_day = current_day
            end_day = start_day + required_days[city] - 1
            # Check special constraints:
            if city == "Warsaw":
                # Must attend the show on days 1-2.
                if start_day > 1 or end_day < 2:
                    valid_schedule = False
                    break
            if city == "Riga":
                # The wedding in Riga must occur between day 11 and day 17.
                # Check that there is an overlap between [start_day, end_day] and [11, 17].
                wedding_start, wedding_end = wedding_window
                if end_day < wedding_start or start_day > wedding_end:
                    valid_schedule = False
                    break
            
            # Add the segment to the itinerary.
            day_range_str = f"Day {start_day}-{end_day}"
            schedule.append({"day_range": day_range_str, "place": city})
            
            # For all segments except the last, the flight day is the last day of the current segment.
            if index < len(itinerary_order) - 1:
                current_day = end_day  # Overlap: flight day is counted in both cities.
            else:
                current_day = end_day
        
        if not valid_schedule:
            continue
        
        # Verify that the computed schedule exactly fits the total number of days.
        if current_day == total_days:
            valid_itinerary = schedule
            break

    # Output the result in a JSON-formatted dictionary.
    result = {"itinerary": valid_itinerary if valid_itinerary is not None else []}
    print(json.dumps(result))

if __name__ == "__main__":
    main()