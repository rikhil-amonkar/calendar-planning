import json

def main():
    # Define the graph of direct flights (bidirectional)
    graph = {
        'Riga': ['Stockholm', 'Istanbul', 'Amsterdam', 'Brussels', 'Munich', 'Prague'],
        'Stockholm': ['Riga', 'Brussels', 'Split', 'Amsterdam', 'Vienna', 'Istanbul', 'Prague', 'Munich'],
        'Brussels': ['Stockholm', 'Vienna', 'Munich', 'Prague', 'Istanbul', 'Riga', 'Seville'],
        'Istanbul': ['Munich', 'Riga', 'Vienna', 'Stockholm', 'Amsterdam', 'Brussels'],
        'Prague': ['Split', 'Munich', 'Amsterdam', 'Brussels', 'Istanbul', 'Riga', 'Stockholm', 'Vienna'],
        'Munich': ['Istanbul', 'Amsterdam', 'Brussels', 'Prague', 'Split', 'Stockholm', 'Seville', 'Riga'],
        'Split': ['Prague', 'Munich', 'Amsterdam', 'Stockholm', 'Vienna'],
        'Amsterdam': ['Munich', 'Split', 'Stockholm', 'Riga', 'Seville', 'Istanbul', 'Vienna'],
        'Vienna': ['Brussels', 'Riga', 'Stockholm', 'Istanbul', 'Seville', 'Prague', 'Split', 'Amsterdam', 'Munich'],
        'Seville': ['Brussels', 'Amsterdam', 'Vienna', 'Munich']
    }
    
    # Define the required days per city
    req_days = {
        'Prague': 5,
        'Brussels': 2,
        'Riga': 2,
        'Munich': 2,
        'Seville': 3,
        'Stockholm': 2,
        'Istanbul': 2,
        'Amsterdam': 3,
        'Vienna': 5,
        'Split': 3
    }
    
    # Fixed events constraints
    fixed_events = {
        'Vienna': [1, 5],
        'Prague': [5, 9],
        'Riga': [15, 16],
        'Split': [11, 13],
        'Stockholm': [16, 17]
    }
    
    # We know the first two cities must be Vienna and Prague to meet fixed events
    # Start at day 1
    itinerary = []
    # Start with Vienna from day 1 to 5
    itinerary.append((1, 5, 'Vienna'))
    # Then Prague from day 5 to 9
    itinerary.append((5, 9, 'Prague'))
    current_day = 9
    visited = {'Vienna', 'Prague'}
    last_city = 'Prague'
    
    # The remaining cities to visit
    remaining = set(req_days.keys()) - visited
    
    # DFS function to find valid itinerary
    def dfs(itinerary, current_day, last_city, visited):
        # If all cities are visited and we've reached day 20
        if len(visited) == len(req_days):
            if current_day == 20:
                return itinerary
            return None
        
        # Try each remaining city
        for city in remaining - visited:
            # Check flight connection
            if city not in graph[last_city]:
                continue
                
            days_needed = req_days[city]
            # If we exceed 20 days, skip
            if current_day + days_needed > 20:
                continue
                
            # Create the block for this city
            start_day = current_day
            end_day = current_day + days_needed
            block = (start_day, end_day, city)
            
            # Temporarily add this block
            new_itinerary = itinerary + [block]
            new_visited = visited | {city}
            new_day = end_day
            new_last_city = city
            
            # Recurse
            result = dfs(new_itinerary, new_day, new_last_city, new_visited)
            if result is not None:
                return result
                
        return None
    
    # Start DFS from day 9, after Prague
    final_itinerary = dfs(itinerary, current_day, last_city, visited)
    
    if final_itinerary is None:
        print('No valid itinerary found.')
        return
    
    # Format the itinerary for output
    itinerary_list = []
    for block in final_itinerary:
        s, e, city = block
        day_range = f"Day {s}-{e}"
        itinerary_list.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()