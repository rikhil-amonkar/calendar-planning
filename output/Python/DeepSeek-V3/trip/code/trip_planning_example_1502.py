import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 27
    city_stays = {
        'Santorini': 3,
        'Valencia': 4,
        'Madrid': 2,
        'Seville': 2,
        'Bucharest': 3,
        'Vienna': 4,
        'Riga': 4,
        'Tallinn': 5,
        'Krakow': 5,
        'Frankfurt': 4
    }
    events = [
        {'city': 'Madrid', 'day_range': (6, 7)},
        {'city': 'Vienna', 'day_range': (3, 6)},
        {'city': 'Riga', 'day_range': (20, 23)},
        {'city': 'Tallinn', 'day_range': (23, 27)},
        {'city': 'Krakow', 'day_range': (11, 15)}
    ]
    
    direct_flights = {
        'Vienna': ['Bucharest', 'Seville', 'Valencia', 'Madrid', 'Krakow', 'Frankfurt', 'Riga', 'Santorini'],
        'Bucharest': ['Vienna', 'Riga', 'Valencia', 'Santorini', 'Frankfurt', 'Madrid'],
        'Santorini': ['Madrid', 'Bucharest', 'Vienna'],
        'Madrid': ['Santorini', 'Valencia', 'Seville', 'Vienna', 'Frankfurt', 'Bucharest'],
        'Seville': ['Valencia', 'Vienna', 'Madrid'],
        'Valencia': ['Seville', 'Madrid', 'Bucharest', 'Vienna', 'Krakow', 'Frankfurt'],
        'Riga': ['Bucharest', 'Tallinn', 'Vienna', 'Frankfurt'],
        'Tallinn': ['Riga', 'Frankfurt'],
        'Krakow': ['Valencia', 'Frankfurt', 'Vienna'],
        'Frankfurt': ['Valencia', 'Krakow', 'Vienna', 'Tallinn', 'Bucharest', 'Riga', 'Madrid']
    }
    
    # Determine fixed events
    fixed_assignments = {}
    for event in events:
        city = event['city']
        start, end = event['day_range']
        for day in range(start, end + 1):
            fixed_assignments[day] = city
    
    # Generate all possible city orders
    cities = list(city_stays.keys())
    
    # Function to check if flight is possible
    def can_fly(from_city, to_city):
        return to_city in direct_flights.get(from_city, [])
    
    # Function to check if an itinerary is valid
    def is_valid(itinerary):
        # Check all cities are visited exactly once
        if sorted(itinerary) != sorted(cities):
            return False
        
        # Check flights are possible
        for i in range(len(itinerary) - 1):
            if not can_fly(itinerary[i], itinerary[i+1]):
                return False
        
        return True
    
    # Find all valid permutations
    valid_orders = []
    for perm in permutations(cities):
        if is_valid(perm):
            valid_orders.append(perm)
    
    if not valid_orders:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Select first valid order (could implement more sophisticated selection)
    selected_order = valid_orders[0]
    
    # Assign days to cities considering fixed events
    itinerary = []
    current_day = 1
    remaining_stays = city_stays.copy()
    
    for city in selected_order:
        # Check if city has fixed days
        fixed_days = [day for day, c in fixed_assignments.items() if c == city]
        
        if fixed_days:
            min_day = min(fixed_days)
            max_day = max(fixed_days)
            # Days before fixed period
            if current_day < min_day:
                pre_days = min_day - current_day
                if pre_days > 0 and remaining_stays[city] > (max_day - min_day + 1):
                    stay_days = min(pre_days, remaining_stays[city] - (max_day - min_day + 1))
                    itinerary.append({'day_range': f'Day {current_day}-{current_day + stay_days - 1}', 'place': city})
                    remaining_stays[city] -= stay_days
                    current_day += stay_days
            # Fixed period
            itinerary.append({'day_range': f'Day {min_day}-{max_day}', 'place': city})
            remaining_stays[city] -= (max_day - min_day + 1)
            current_day = max_day + 1
            # Days after fixed period
            if remaining_stays[city] > 0:
                itinerary.append({'day_range': f'Day {current_day}-{current_day + remaining_stays[city] - 1}', 'place': city})
                current_day += remaining_stays[city]
        else:
            stay_days = remaining_stays[city]
            itinerary.append({'day_range': f'Day {current_day}-{current_day + stay_days - 1}', 'place': city})
            current_day += stay_days
        
        # Add flight if not last city
        if city != selected_order[-1]:
            next_city = selected_order[selected_order.index(city) + 1]
            itinerary.append({'flying': f'Day {current_day-1}-{current_day-1}', 'from': city, 'to': next_city})
    
    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()