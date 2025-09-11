import json
from collections import defaultdict

def main():
    # Define the graph of direct flights
    graph = {
        'Barcelona': ['Copenhagen', 'Venice', 'Stuttgart', 'Split', 'Oslo', 'Brussels'],
        'Oslo': ['Brussels', 'Split', 'Venice', 'Copenhagen', 'Barcelona'],
        'Stuttgart': ['Venice', 'Barcelona', 'Copenhagen', 'Split'],
        'Venice': ['Stuttgart', 'Barcelona', 'Brussels', 'Copenhagen', 'Oslo'],
        'Split': ['Copenhagen', 'Oslo', 'Barcelona', 'Stuttgart'],
        'Brussels': ['Venice', 'Oslo', 'Copenhagen', 'Barcelona'],
        'Copenhagen': ['Split', 'Barcelona', 'Brussels', 'Oslo', 'Stuttgart', 'Venice']
    }
    
    # Required days per city
    required_days = {
        'Barcelona': 3,
        'Oslo': 2,
        'Stuttgart': 3,
        'Venice': 4,
        'Split': 4,
        'Brussels': 3,
        'Copenhagen': 3
    }
    
    # Fixed day constraints
    fixed_constraints = {
        1: ['Barcelona'],
        2: ['Barcelona'],
        3: ['Barcelona', 'Oslo'],
        4: ['Oslo'],
        9: ['Brussels'],
        10: ['Brussels'],
        11: ['Brussels']
    }
    
    # Initialize variables for DFS
    days = 16
    cities_list = list(required_days.keys())
    
    # We'll use DFS to find a valid itinerary
    def dfs(day, current_city, days_spent, itinerary):
        if day > days:
            if all(days_spent[city] == required_days[city] for city in cities_list):
                return itinerary
            return None
        
        # Check fixed constraints for the current day
        if day in fixed_constraints:
            for city in fixed_constraints[day]:
                if city != current_city and (not itinerary or itinerary[-1][1] != city):
                    return None
        
        # Option 1: Stay in the current city
        new_days_spent = days_spent.copy()
        new_days_spent[current_city] += 1
        if new_days_spent[current_city] <= required_days[current_city]:
            new_itinerary = itinerary + [(day, current_city)]
            result = dfs(day + 1, current_city, new_days_spent, new_itinerary)
            if result is not None:
                return result
        
        # Option 2: Fly to a connected city
        for next_city in graph[current_city]:
            new_days_spent = days_spent.copy()
            new_days_spent[current_city] += 1
            new_days_spent[next_city] += 1
            if new_days_spent[current_city] > required_days[current_city] or new_days_spent[next_city] > required_days[next_city]:
                continue
            new_itinerary = itinerary + [(day, current_city, next_city)]
            result = dfs(day + 1, next_city, new_days_spent, new_itinerary)
            if result is not None:
                return result
        
        return None
    
    # Start from day 1 in Barcelona
    initial_days_spent = defaultdict(int)
    initial_days_spent['Barcelona'] = 1
    itinerary = dfs(2, 'Barcelona', initial_days_spent, [(1, 'Barcelona')])
    
    if itinerary is None:
        print('{"itinerary": []}')
        return
    
    # Process the itinerary to determine city presence per day
    city_days = defaultdict(list)
    for entry in itinerary:
        day = entry[0]
        if len(entry) == 2:
            city = entry[1]
            city_days[city].append(day)
        else:
            city1, city2 = entry[1], entry[2]
            city_days[city1].append(day)
            city_days[city2].append(day)
    
    # Create continuous ranges for each city
    ranges = []
    for city, days_list in city_days.items():
        days_list.sort()
        start = days_list[0]
        for i in range(1, len(days_list)):
            if days_list[i] != days_list[i-1] + 1:
                ranges.append((start, days_list[i-1], city))
                start = days_list[i]
        ranges.append((start, days_list[-1], city))
    
    # Sort ranges by start day
    ranges.sort(key=lambda x: x[0])
    
    # Convert to JSON output format
    output_list = []
    for start, end, city in ranges:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        output_list.append({"day_range": day_range, "place": city})
    
    print(json.dumps({"itinerary": output_list}))

if __name__ == '__main__':
    main()