import json
from itertools import permutations

def find_valid_itinerary():
    # Define cities and their required days
    cities = {
        'Brussels': 2,
        'Venice': 3,
        'Madrid': 5,
        'London': 3,
        'Lisbon': 4,
        'Reykjavik': 3,
        'Santorini': 3
    }
    
    # Define flight connections (undirected)
    flights = {
        'Venice': ['Madrid', 'Brussels', 'Santorini', 'Lisbon', 'London'],
        'Madrid': ['Venice', 'Reykjavik', 'London', 'Santorini', 'Lisbon', 'Brussels'],
        'Lisbon': ['Reykjavik', 'Venice', 'London', 'Madrid', 'Brussels'],
        'Reykjavik': ['Lisbon', 'Madrid', 'London', 'Brussels'],
        'Brussels': ['Venice', 'London', 'Lisbon', 'Madrid', 'Reykjavik'],
        'London': ['Brussels', 'Madrid', 'Santorini', 'Lisbon', 'Reykjavik', 'Venice'],
        'Santorini': ['Venice', 'Madrid', 'London']
    }
    
    # Fixed constraints
    fixed_events = [
        {'place': 'Brussels', 'day_range': (1, 2)},
        {'place': 'Venice', 'day_range': (5, 7)},
        {'place': 'Madrid', 'day_range': (7, 11)}
    ]
    
    # Other cities to place (excluding fixed days)
    remaining_days = 17
    fixed_days = set()
    for event in fixed_events:
        start, end = event['day_range']
        fixed_days.update(range(start, end + 1))
        remaining_days -= (end - start + 1)
    
    # Other cities and their days
    other_cities = {
        'London': 3,
        'Lisbon': 4,
        'Reykjavik': 3,
        'Santorini': 3
    }
    
    # Generate possible orders for other cities
    city_names = list(other_cities.keys())
    city_days = list(other_cities.values())
    
    # Try all permutations of remaining cities
    for perm in permutations(city_names):
        itinerary = []
        current_day = 1
        day_allocations = {}
        
        # Place fixed events first
        for event in fixed_events:
            start, end = event['day_range']
            day_allocations.update({day: event['place'] for day in range(start, end + 1)})
        
        # Try to place remaining cities in available days
        remaining_cities = list(perm)
        remaining_days_list = city_days.copy()
        
        for day in range(1, 18):
            if day in day_allocations:
                continue
            
            if not remaining_cities:
                break
            
            current_city = remaining_cities[0]
            if day_allocations.get(day - 1) == current_city or (day == 1 and not day_allocations.get(1)):
                # Continue current city if possible
                day_allocations[day] = current_city
                remaining_days_list[0] -= 1
                if remaining_days_list[0] == 0:
                    remaining_cities.pop(0)
                    remaining_days_list.pop(0)
            else:
                # Need to fly to next city
                prev_city = None
                for d in range(day - 1, 0, -1):
                    if d in day_allocations:
                        prev_city = day_allocations[d]
                        break
                
                if prev_city is None:
                    prev_city = 'Brussels'  # Starting point
                
                next_city = remaining_cities[0]
                if next_city in flights.get(prev_city, []):
                    day_allocations[day] = next_city
                    remaining_days_list[0] -= 1
                    if remaining_days_list[0] == 0:
                        remaining_cities.pop(0)
                        remaining_days_list.pop(0)
                else:
                    break
        
        # Check if all cities are placed
        if len(remaining_cities) == 0:
            # Convert day_allocations to itinerary
            itinerary = []
            current_place = None
            start_day = 1
            
            for day in range(1, 18):
                place = day_allocations.get(day)
                if place != current_place:
                    if current_place is not None:
                        itinerary.append({
                            'day_range': f'Day {start_day}-{day - 1}',
                            'place': current_place
                        })
                    if place is not None:
                        # Add flight if not first location
                        if current_place is not None:
                            itinerary.append({
                                'flying': f'Day {day}-{day}',
                                'from': current_place,
                                'to': place
                            })
                    start_day = day
                    current_place = place
            
            if current_place is not None:
                itinerary.append({
                    'day_range': f'Day {start_day}-17',
                    'place': current_place
                })
            
            return itinerary
    
    return None

def main():
    itinerary = find_valid_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()