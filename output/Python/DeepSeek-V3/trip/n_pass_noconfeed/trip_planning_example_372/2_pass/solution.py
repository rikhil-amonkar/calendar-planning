import json
from itertools import permutations

def find_itinerary():
    # Input constraints
    total_days = 13
    city_stays = {
        'Porto': 3,
        'Seville': 2,
        'Madrid': 4,
        'Stuttgart': 7
    }
    conference_days = {7, 13}
    relatives_madrid_days = (1, 4)
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
        # Try inserting Stuttgart in all possible positions
        for insert_pos in range(len(order) + 1):
            # Create the potential itinerary order
            itinerary_order = list(order[:insert_pos]) + ['Stuttgart'] + list(order[insert_pos:])
            
            # Check if this order satisfies all constraints
            current_day = 1
            prev_city = None
            itinerary = []
            valid = True
            
            for city in itinerary_order:
                # Check flight connection if not first city
                if prev_city is not None and city not in direct_flights[prev_city]:
                    valid = False
                    break
                
                start_day = current_day
                end_day = current_day + city_stays[city] - 1
                itinerary.append((start_day, end_day, city))
                
                # Move to next city
                current_day = end_day + 1
                prev_city = city
            
            # Check if we completed all days correctly
            if not valid or current_day - 1 != total_days:
                continue
            
            # Check Stuttgart conference days
            stuttgart_visit = next((visit for visit in itinerary if visit[2] == 'Stuttgart'), None)
            if not stuttgart_visit:
                continue
                
            stuttgart_start, stuttgart_end, _ = stuttgart_visit
            if not (stuttgart_start <= 7 <= stuttgart_end and stuttgart_start <= 13 <= stuttgart_end):
                continue
            
            # Check Madrid relatives visit
            madrid_visit = next((visit for visit in itinerary if visit[2] == 'Madrid'), None)
            if not madrid_visit:
                continue
                
            madrid_start, madrid_end, _ = madrid_visit
            if not (madrid_start <= 1 and madrid_end >= 4):
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