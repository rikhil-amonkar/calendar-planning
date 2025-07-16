import json
from itertools import permutations

def find_itinerary():
    cities = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }
    
    constraints = {
        'Helsinki': {'meet_friends': (3, 5)},  # Must be in Helsinki between days 3-5
        'Vienna': {'annual_show': (2, 3)},     # Must be in Vienna between days 2-3
        'Tallinn': {'wedding': (7, 11)}         # Must be in Tallinn between days 7-11
    }
    
    direct_flights = {
        'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Vienna': ['Riga', 'Dublin', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Tallinn': ['Dublin', 'Helsinki', 'Riga'],
        'Dublin': ['Riga', 'Vienna', 'Reykjavik', 'Tallinn', 'Helsinki']
    }
    
    city_list = list(cities.keys())
    
    # We'll try all possible permutations of the cities
    for perm in permutations(city_list):
        itinerary = []
        current_city = None
        remaining_days = cities.copy()
        day = 1
        valid = True
        
        for city in perm:
            # Check flight connection
            if current_city is not None and city not in direct_flights[current_city]:
                valid = False
                break
            
            max_possible_days = remaining_days[city]
            days_to_spend = max_possible_days
            
            # Adjust days based on constraints
            if city == 'Helsinki':
                start, end = constraints['Helsinki']['meet_friends']
                # Must be in Helsinki during days 3-5
                # Calculate overlap between planned stay and required days
                stay_start = day
                stay_end = day + days_to_spend - 1
                if stay_end < start or stay_start > end:
                    valid = False
                    break
                # Adjust days to ensure we cover the required period
                days_to_spend = min(days_to_spend, end - stay_start + 1)
                
            elif city == 'Vienna':
                start, end = constraints['Vienna']['annual_show']
                stay_start = day
                stay_end = day + days_to_spend - 1
                if stay_end < start or stay_start > end:
                    valid = False
                    break
                days_to_spend = min(days_to_spend, end - stay_start + 1)
                
            elif city == 'Tallinn':
                start, end = constraints['Tallinn']['wedding']
                stay_start = day
                stay_end = day + days_to_spend - 1
                if stay_end < start or stay_start > end:
                    valid = False
                    break
                days_to_spend = min(days_to_spend, end - stay_start + 1)
            
            # Add to itinerary
            itinerary.append({
                'day_range': f"Day {day}-{day + days_to_spend - 1}",
                'place': city
            })
            
            day += days_to_spend
            remaining_days[city] -= days_to_spend
            current_city = city
            
            # Check if we've exceeded 15 days
            if day > 15:
                valid = False
                break
        
        # Check if we've used exactly 15 days and visited all cities
        if valid and day == 16 and all(v == 0 for v in remaining_days.values()):
            return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))