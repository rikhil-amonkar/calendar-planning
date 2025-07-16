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
        'Tallinn': {'wedding': (7, 11)}        # Must be in Tallinn between days 7-11
    }
    
    direct_flights = {
        'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Vienna': ['Riga', 'Dublin', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Tallinn': ['Dublin', 'Helsinki', 'Riga'],
        'Dublin': ['Riga', 'Vienna', 'Reykjavik', 'Tallinn', 'Helsinki']
    }
    
    # Try different city orders
    for perm in permutations(cities.keys()):
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
            
            days_available = remaining_days[city]
            days_to_spend = days_available
            
            # Handle city-specific constraints
            if city == 'Helsinki':
                # Must be in Helsinki days 3-5
                if day > 3:
                    valid = False
                    break
                days_to_spend = max(days_to_spend, 3)  # Need at least 3 days
                stay_end = day + days_to_spend - 1
                if stay_end < 5:
                    valid = False
                    break
                
            elif city == 'Vienna':
                # Must be in Vienna days 2-3
                if day > 2:
                    valid = False
                    break
                days_to_spend = 2  # Exactly 2 days needed
                stay_end = day + days_to_spend - 1
                if stay_end < 3:
                    valid = False
                    break
                
            elif city == 'Tallinn':
                # Must be in Tallinn days 7-11
                if day > 7:
                    valid = False
                    break
                if day + days_to_spend - 1 < 11:
                    days_to_spend = 11 - day + 1
                if days_to_spend > remaining_days[city]:
                    valid = False
                    break
                stay_end = day + days_to_spend - 1
                if stay_end > 11:
                    valid = False
                    break
            
            # Add to itinerary
            itinerary.append({
                'day_range': f"Day {day}-{day + days_to_spend - 1}",
                'place': city
            })
            
            day += days_to_spend
            remaining_days[city] -= days_to_spend
            current_city = city
            
            if day > 15:
                valid = False
                break
        
        # Check if all days are used and all cities visited
        if valid and day == 16 and all(v == 0 for v in remaining_days.values()):
            # Verify all constraints are met
            constraint_met = True
            for entry in itinerary:
                city = entry['place']
                day_start = int(entry['day_range'].split('-')[0][4:])
                day_end = int(entry['day_range'].split('-')[1][4:])
                
                if city == 'Helsinki':
                    if not (day_start <= 3 and day_end >= 5):
                        constraint_met = False
                        break
                elif city == 'Vienna':
                    if not (day_start <= 2 and day_end >= 3):
                        constraint_met = False
                        break
                elif city == 'Tallinn':
                    if not (day_start <= 11 and day_end >= 7):
                        constraint_met = False
                        break
            
            if constraint_met:
                return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))