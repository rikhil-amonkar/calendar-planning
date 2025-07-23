import json
from itertools import permutations

def find_itinerary():
    # Input constraints
    total_days = 13
    city_stays = {
        'Seville': 2,
        'Stuttgart': 7,
        'Porto': 3,
        'Madrid': 4
    }
    conference_days = [7, 13]
    relatives_madrid_days = (1, 4)
    direct_flights = {
        'Porto': ['Stuttgart', 'Seville', 'Madrid'],
        'Seville': ['Porto', 'Madrid'],
        'Madrid': ['Porto', 'Seville'],
        'Stuttgart': ['Porto']
    }
    
    # Correcting city names to match flight data
    city_stays_corrected = {
        'Porto': city_stays['Porto'],
        'Seville': city_stays['Seville'],
        'Madrid': city_stays['Madrid'],
        'Stuttgart': city_stays['Stuttgart']
    }
    
    cities = list(city_stays_corrected.keys())
    
    # Generate all possible orders of visiting cities
    possible_orders = permutations([city for city in cities if city != 'Stuttgart'])
    
    valid_itineraries = []
    
    for order in possible_orders:
        # Stuttgart must be in the itinerary where conferences are on day 7 and 13
        # We need to insert Stuttgart in the order appropriately
        # Trying all possible positions for Stuttgart
        for i in range(len(order) + 1):
            temp_order = list(order[:i]) + ['Stuttgart'] + list(order[i:])
            itinerary = []
            current_day = 1
            prev_city = None
            
            for city in temp_order:
                if prev_city is None:
                    itinerary.append((current_day, current_day + city_stays_corrected[city] - 1, city))
                    current_day += city_stays_corrected[city]
                    prev_city = city
                else:
                    # Check if there's a direct flight
                    if city in direct_flights[prev_city] or prev_city in direct_flights[city]:
                        # Transition day is current_day, counts for both cities
                        itinerary.append((current_day, current_day + city_stays_corrected[city] - 1, city))
                        current_day += city_stays_corrected[city]
                        prev_city = city
                    else:
                        break
            else:
                # Check if total days match and Stuttgart conferences are on correct days
                if current_day - 1 == total_days:
                    stuttgart_days = [day for (start, end, city) in itinerary if city == 'Stuttgart']
                    if stuttgart_days:
                        start, end, _ = stuttgart_days[0]
                        stuttgart_conference_days_present = all(
                            start <= day <= end for day in conference_days
                        )
                        madrid_days = [day for (start, end, city) in itinerary if city == 'Madrid']
                        if madrid_days:
                            madrid_start, madrid_end, _ = madrid_days[0]
                            madrid_relatives_ok = (
                                madrid_start <= relatives_madrid_days[0] and 
                                madrid_end >= relatives_madrid_days[1]
                            )
                            if stuttgart_conference_days_present and madrid_relatives_ok:
                                valid_itineraries.append(itinerary)
    
    # Select the first valid itinerary (assuming it meets all constraints)
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
    print(json.dumps(itinerary))