import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 16
    city_stays = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    
    # Constraints
    constraints = {
        'Milan': {'wedding': (11, 13)},
        'Krakow': {'meet_friends': (8, 9)},
        'Munich': {'show': (4, 8)}
    }
    
    # Direct flights
    direct_flights = {
        'Munich': ['Porto', 'Krakow', 'Milan', 'Dubrovnik', 'Split'],
        'Porto': ['Munich', 'Milan'],
        'Milan': ['Porto', 'Split', 'Munich', 'Krakow'],
        'Split': ['Milan', 'Krakow', 'Munich'],
        'Krakow': ['Munich', 'Split', 'Milan'],
        'Dubrovnik': ['Munich']
    }
    
    # Check if two cities are connected
    def is_connected(city1, city2):
        return city2 in direct_flights.get(city1, []) or city1 in direct_flights.get(city2, [])
    
    # Generate all possible city orders
    cities = list(city_stays.keys())
    possible_orders = permutations(cities)
    
    # Function to check if an order satisfies all constraints
    def is_valid_order(order):
        day = 1
        itinerary = []
        prev_city = None
        
        for city in order:
            if prev_city and not is_connected(prev_city, city):
                return False
            
            stay_duration = city_stays[city]
            end_day = day + stay_duration - 1
            
            # Check constraints for current city
            if city in constraints:
                for constraint, (start_con, end_con) in constraints[city].items():
                    if not (day <= start_con and end_day >= end_con):
                        return False
            
            day = end_day + 1
            prev_city = city
        
        return day - 1 == total_days
    
    # Find a valid order
    valid_order = None
    for order in possible_orders:
        if is_valid_order(order):
            valid_order = order
            break
    
    if not valid_order:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Generate itinerary
    itinerary = []
    day = 1
    prev_city = None
    
    for city in valid_order:
        stay_duration = city_stays[city]
        end_day = day + stay_duration - 1
        
        if prev_city:
            itinerary.append({
                'flying': f'Day {day-1}-{day-1}',
                'from': prev_city,
                'to': city
            })
        
        itinerary.append({
            'day_range': f'Day {day}-{end_day}',
            'place': city
        })
        
        day = end_day + 1
        prev_city = city
    
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()