import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 25
    cities = {
        'Warsaw': 4,
        'Venice': 3,
        'Vilnius': 3,
        'Salzburg': 4,
        'Amsterdam': 2,
        'Barcelona': 5,
        'Paris': 2,
        'Hamburg': 4,
        'Florence': 5,
        'Tallinn': 2
    }
    
    constraints = {
        'Salzburg': {'day_range': (22, 25)},
        'Barcelona': {'day_range': (2, 6)},
        'Paris': {'day_range': (1, 2)},
        'Hamburg': {'day_range': (19, 22)},
        'Tallinn': {'day_range': (11, 12)}
    }
    
    direct_flights = {
        'Paris': ['Venice', 'Hamburg', 'Vilnius', 'Amsterdam', 'Florence', 'Warsaw', 'Tallinn', 'Barcelona'],
        'Barcelona': ['Amsterdam', 'Warsaw', 'Hamburg', 'Florence', 'Venice', 'Tallinn'],
        'Amsterdam': ['Warsaw', 'Vilnius', 'Hamburg', 'Venice', 'Tallinn', 'Florence'],
        'Warsaw': ['Venice', 'Vilnius', 'Hamburg', 'Tallinn'],
        'Venice': ['Hamburg'],
        'Vilnius': ['Tallinn'],
        'Hamburg': ['Salzburg'],
        'Tallinn': ['Vilnius'],
        'Florence': [],
        'Salzburg': []
    }
    
    # Correct typo in Venice
    direct_flights['Barcelona'].remove('Venice')
    direct_flights['Barcelona'].append('Venice')
    direct_flights['Warsaw'].remove('Venice')
    direct_flights['Warsaw'].append('Venice')
    
    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)
    
    def is_valid_order(order):
        # Check if the order satisfies all constraints
        day = 1
        prev_city = None
        for city in order:
            if prev_city is not None and city not in direct_flights[prev_city]:
                return False
            if city in constraints:
                start, end = constraints[city]['day_range']
                if not (day <= start and day + cities[city] - 1 >= end):
                    return False
            day += cities[city]
            prev_city = city
        return day - 1 <= total_days
    
    valid_orders = []
    for order in possible_orders:
        if is_valid_order(order):
            valid_orders.append(order)
    
    if not valid_orders:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Select the first valid order (can be enhanced with more optimal criteria)
    selected_order = valid_orders[0]
    
    # Generate itinerary
    itinerary = []
    current_day = 1
    prev_city = None
    
    for city in selected_order:
        duration = cities[city]
        end_day = current_day + duration - 1
        
        if prev_city is not None:
            itinerary.append({
                'flying': f'Day {current_day-1}-{current_day-1}',
                'from': prev_city,
                'to': city
            })
        
        itinerary.append({
            'day_range': f'Day {current_day}-{end_day}',
            'place': city
        })
        
        current_day = end_day + 1
        prev_city = city
    
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()