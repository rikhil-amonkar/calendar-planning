import json
from itertools import permutations

def find_itinerary():
    # Input constraints
    total_days = 13
    city_stays = {
        'Porto': 3,
        'Seville': 2,
        'Madrid': 4,
        'Stuttgart': 7  # Total days in Stuttgart
    }
    conference_days = {7, 13}
    relatives_madrid_days = (1, 4)  # Must be in Madrid from day 1 to day 4
    direct_flights = {
        'Porto': ['Stuttgart', 'Seville', 'Madrid'],
        'Seville': ['Porto', 'Madrid'],
        'Madrid': ['Porto', 'Seville'],
        'Stuttgart': ['Porto']
    }
    
    cities = list(city_stays.keys())
    
    # Generate all possible orders of visiting cities (excluding Stuttgart)
    other_cities = [city for city in cities if city != 'Stuttgart']
    possible_orders = permutations(other_cities)
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Try inserting Stuttgart in all possible positions (can appear multiple times)
        # We'll try up to 3 Stuttgart visits (since total Stuttgart days is 7)
        for stuttgart_positions in [(i,) for i in range(len(order)+1)] + \
                                  [(i,j) for i in range(len(order)+1) for j in range(i+1, len(order)+2)]:
            
            # Create the potential itinerary order with Stuttgart inserted
            temp_order = list(order)
            for pos in sorted(stuttgart_positions, reverse=True):
                temp_order.insert(pos, 'Stuttgart')
            itinerary_order = temp_order
            
            # Now we need to distribute the Stuttgart days (7 total) across visits
            stuttgart_indices = [i for i, city in enumerate(itinerary_order) if city == 'Stuttgart']
            num_stuttgart_visits = len(stuttgart_indices)
            
            # Try all possible ways to split 7 days across the Stuttgart visits
            from itertools import product
            possible_splits = []
            if num_stuttgart_visits == 1:
                possible_splits = [(7,)]
            elif num_stuttgart_visits == 2:
                possible_splits = [(i, 7-i) for i in range(1,7)]
            elif num_stuttgart_visits == 3:
                possible_splits = [(i,j,k) for i in range(1,6) for j in range(1,6) 
                                 for k in range(1,6) if i+j+k == 7]
            
            for split in possible_splits:
                # Assign stay durations to each city
                stay_durations = {}
                stuttgart_count = 0
                for city in itinerary_order:
                    if city == 'Stuttgart':
                        stay_durations[city] = split[stuttgart_count]
                        stuttgart_count += 1
                    else:
                        stay_durations[city] = city_stays[city]
                
                # Now build the itinerary with these durations
                current_day = 1
                prev_city = None
                itinerary = []
                valid = True
                stuttgart_visits = []
                
                for city in itinerary_order:
                    # Check flight connection if not first city
                    if prev_city is not None and city not in direct_flights.get(prev_city, []):
                        valid = False
                        break
                    
                    start_day = current_day
                    end_day = current_day + stay_durations[city] - 1
                    itinerary.append((start_day, end_day, city))
                    
                    if city == 'Stuttgart':
                        stuttgart_visits.append((start_day, end_day))
                    
                    # Move to next city
                    current_day = end_day + 1
                    prev_city = city
                
                # Check if we completed all days correctly
                if not valid or current_day - 1 != total_days:
                    continue
                
                # Check conference days are during Stuttgart visits
                conf_days_covered = set()
                for (start, end) in stuttgart_visits:
                    for day in conference_days:
                        if start <= day <= end:
                            conf_days_covered.add(day)
                if conf_days_covered != conference_days:
                    continue
                
                # Check Madrid relatives visit is exactly days 1-4
                madrid_visit = next((visit for visit in itinerary if visit[2] == 'Madrid'), None)
                if not madrid_visit:
                    continue
                
                madrid_start, madrid_end, _ = madrid_visit
                if not (madrid_start == 1 and madrid_end == 4):
                    continue
                
                # If we got here, it's a valid itinerary
                valid_itineraries.append(itinerary)
    
    # Prepare the output
    if valid_itineraries:
        best_itinerary = valid_itineraries[0]
        result = {
            "itinerary": [
                {"day_range": f"Day {start}-{end}", "place": place}
                for (start, end, place) in best_itinerary
            ]
        }
    else:
        result = {"itinerary": []}
    
    return result

if __name__ == "__main__":
    itinerary = find_itinerary()
    print(json.dumps(itinerary, indent=2))