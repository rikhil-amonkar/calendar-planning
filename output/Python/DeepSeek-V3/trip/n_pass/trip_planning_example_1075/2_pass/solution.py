import json
from itertools import permutations

def find_itinerary():
    # Cities and required days
    cities = {
        'Vienna': 4,
        'Lyon': 3,
        'Edinburgh': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Manchester': 2,
        'Split': 5,
        'Prague': 4
    }
    
    # Direct flights
    flights = {
        'Reykjavik': ['Stuttgart', 'Vienna', 'Prague'],
        'Stuttgart': ['Reykjavik', 'Split', 'Vienna', 'Edinburgh', 'Manchester'],
        'Vienna': ['Stuttgart', 'Prague', 'Manchester', 'Lyon', 'Split', 'Reykjavik'],
        'Prague': ['Manchester', 'Edinburgh', 'Vienna', 'Split', 'Lyon', 'Reykjavik'],
        'Edinburgh': ['Prague', 'Stuttgart'],
        'Manchester': ['Prague', 'Vienna', 'Split', 'Stuttgart'],
        'Split': ['Stuttgart', 'Manchester', 'Prague', 'Vienna', 'Lyon'],
        'Lyon': ['Vienna', 'Split', 'Prague']
    }
    
    # Fixed constraints
    fixed_events = [
        {'city': 'Edinburgh', 'day_range': (5, 8)},  # Must be in Edinburgh days 5-8
        {'city': 'Split', 'day_range': (19, 23)}     # Must be in Split days 19-23
    ]
    
    total_days = 25
    
    # Generate all possible city orders (permutations of 8 cities is too large, so we'll limit)
    # Instead, we'll generate permutations but optimize the search
    city_names = list(cities.keys())
    
    # We'll try to build the itinerary step by step with backtracking
    def backtrack(current_itinerary, remaining_days, current_day, visited, prev_city):
        if current_day > total_days:
            return None
        
        # Check if all cities are visited and days are exactly 25
        if all(v == 0 for v in remaining_days.values()) and current_day - 1 == total_days:
            return current_itinerary
        
        # Check fixed events first
        for event in fixed_events:
            event_city = event['city']
            start, end = event['day_range']
            required_days = end - start + 1
            
            # If we haven't visited this city yet and we're approaching its required days
            if remaining_days[event_city] > 0 and current_day <= start:
                # Must visit this city now to cover the event
                if prev_city and event_city not in flights[prev_city]:
                    return None
                
                # Check if we have enough days remaining
                if remaining_days[event_city] < required_days:
                    return None
                
                # Visit this city
                new_itinerary = current_itinerary.copy()
                new_itinerary.append({
                    'day_range': f"Day {start}-{end}",
                    'place': event_city
                })
                new_remaining = remaining_days.copy()
                new_remaining[event_city] -= required_days
                
                result = backtrack(
                    new_itinerary,
                    new_remaining,
                    end + 1,
                    visited | {event_city},
                    event_city
                )
                if result:
                    return result
                return None
        
        # Try other cities if no fixed events are pending
        for city in city_names:
            if remaining_days[city] > 0 and (not prev_city or city in flights[prev_city]):
                # Try visiting this city for all possible durations
                max_days = min(remaining_days[city], total_days - current_day + 1)
                for days in range(max_days, 0, -1):
                    new_itinerary = current_itinerary.copy()
                    end_day = current_day + days - 1
                    new_itinerary.append({
                        'day_range': f"Day {current_day}-{end_day}",
                        'place': city
                    })
                    new_remaining = remaining_days.copy()
                    new_remaining[city] -= days
                    
                    result = backtrack(
                        new_itinerary,
                        new_remaining,
                        end_day + 1,
                        visited | {city},
                        city
                    )
                    if result:
                        return result
        return None
    
    # Start the backtracking
    initial_remaining = cities.copy()
    result = backtrack([], initial_remaining, 1, set(), None)
    
    if not result:
        return {"itinerary": []}
    
    return {"itinerary": result}

# Run the function and print the result
print(json.dumps(find_itinerary()))