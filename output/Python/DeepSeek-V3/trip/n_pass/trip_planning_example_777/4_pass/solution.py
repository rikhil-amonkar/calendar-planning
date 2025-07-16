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
                # We must be in Helsinki during days 3-5
                # Calculate the minimal stay that covers this period
                earliest_start = max(1, start - days_to_spend + 1)
                latest_start = min(end, 15 - days_to_spend + 1)
                
                # Find a start day that covers the required period
                found = False
                for possible_start in range(earliest_start, latest_start + 1):
                    if possible_start <= start and possible_start + days_to_spend - 1 >= end:
                        # Adjust the itinerary to start at this day
                        # Need to fill days before if necessary
                        if possible_start > day:
                            # Need to stay somewhere else first
                            valid = False
                            break
                        days_to_spend = days_to_spend  # Use full duration
                        found = True
                        break
                
                if not found:
                    valid = False
                    break
                
            elif city == 'Vienna':
                start, end = constraints['Vienna']['annual_show']
                # Must be in Vienna during days 2-3
                # The stay must include both days 2 and 3
                if days_to_spend < 2:
                    valid = False
                    break
                if day > start:
                    valid = False
                    break
                days_to_spend = min(days_to_spend, 2)  # Only need 2 days
                
            elif city == 'Tallinn':
                start, end = constraints['Tallinn']['wedding']
                # Must be in Tallinn between days 7-11
                # Calculate possible stay that covers this period
                if day > end:
                    valid = False
                    break
                if day + days_to_spend - 1 < start:
                    valid = False
                    break
                # Adjust days to cover the required period
                required_days = min(days_to_spend, end - day + 1)
                days_to_spend = required_days
            
            # Add to itinerary
            stay_end = day + days_to_spend - 1
            itinerary.append({
                'day_range': f"Day {day}-{stay_end}",
                'place': city
            })
            
            day = stay_end + 1
            remaining_days[city] -= days_to_spend
            current_city = city
            
            # Check if we've exceeded 15 days
            if day > 16:  # Since we increment after adding
                valid = False
                break
        
        # Check if we've used exactly 15 days and visited all cities
        if valid and day == 16 and all(v == 0 for v in remaining_days.values()):
            # Verify all constraints are met
            constraint_met = True
            for entry in itinerary:
                city = entry['place']
                day_start = int(entry['day_range'].split('-')[0][4:])
                day_end = int(entry['day_range'].split('-')[1][4:])
                
                if city == 'Helsinki':
                    start, end = constraints['Helsinki']['meet_friends']
                    if not (day_start <= start and day_end >= end):
                        constraint_met = False
                        break
                elif city == 'Vienna':
                    start, end = constraints['Vienna']['annual_show']
                    if not (day_start <= start and day_end >= end):
                        constraint_met = False
                        break
                elif city == 'Tallinn':
                    start, end = constraints['Tallinn']['wedding']
                    if not (day_start <= start and day_end >= end):
                        constraint_met = False
                        break
            
            if constraint_met:
                return {'itinerary': itinerary}
    
    return {'itinerary': []}

result = find_itinerary()
print(json.dumps(result, indent=2))