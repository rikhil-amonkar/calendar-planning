import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 20
    city_stays = {
        'Paris': 5,
        'Florence': 3,
        'Vienna': 2,
        'Porto': 3,
        'Munich': 5,
        'Nice': 5,
        'Warsaw': 3
    }
    
    # Constraints
    constraints = [
        {'city': 'Porto', 'day_range': (1, 3)},
        {'city': 'Vienna', 'day_range': (19, 20)},
        {'city': 'Warsaw', 'day_range': (13, 15)}
    ]
    
    # Direct flights
    direct_flights = {
        'Florence': ['Vienna', 'Munich', 'Paris'],
        'Vienna': ['Florence', 'Munich', 'Porto', 'Warsaw', 'Paris', 'Nice'],
        'Paris': ['Warsaw', 'Florence', 'Vienna', 'Porto', 'Nice', 'Munich'],
        'Munich': ['Vienna', 'Florence', 'Warsaw', 'Nice', 'Porto', 'Paris'],
        'Porto': ['Vienna', 'Munich', 'Nice', 'Paris', 'Warsaw'],
        'Warsaw': ['Paris', 'Vienna', 'Munich', 'Nice'],
        'Nice': ['Munich', 'Warsaw', 'Porto', 'Paris', 'Vienna']
    }
    
    # Generate all possible city orders
    cities = list(city_stays.keys())
    possible_orders = permutations(cities)
    
    def is_valid_order(order):
        # Check if all constraints are met
        schedule = []
        current_day = 1
        
        for i, city in enumerate(order):
            stay_days = city_stays[city]
            end_day = current_day + stay_days - 1
            
            # Check constraints
            for constraint in constraints:
                if constraint['city'] == city:
                    const_start, const_end = constraint['day_range']
                    if not (const_start >= current_day and const_end <= end_day):
                        return False
            
            # Add to schedule
            schedule.append({
                'city': city,
                'start_day': current_day,
                'end_day': end_day
            })
            
            current_day = end_day + 1
            
            # Check flight connection to next city
            if i < len(order) - 1:
                next_city = order[i+1]
                if next_city not in direct_flights[city]:
                    return False
        
        return schedule if current_day - 1 == total_days else False
    
    # Find a valid order
    valid_schedule = None
    for order in possible_orders:
        schedule = is_valid_order(order)
        if schedule:
            valid_schedule = schedule
            break
    
    if not valid_schedule:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Convert to output format
    output = []
    for i, entry in enumerate(valid_schedule):
        city = entry['city']
        start = entry['start_day']
        end = entry['end_day']
        
        # Add stay
        output.append({
            'day_range': f'Day {start}-{end}',
            'place': city
        })
        
        # Add flight if not last city
        if i < len(valid_schedule) - 1:
            next_city = valid_schedule[i+1]['city']
            output.append({
                'flying': f'Day {end}-{end}',
                'from': city,
                'to': next_city
            })
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()