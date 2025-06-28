import json

def main():
    # Define the constraints
    cities = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Venice', 'Amsterdam', 'Barcelona', 'Porto']  # non-Nice cities
    durations = {
        'Naples': 3,
        'Valencia': 5,
        'Stuttgart': 2,
        'Split': 5,
        'Venice': 5,
        'Amsterdam': 4,
        'Barcelona': 2,
        'Porto': 4,
        'Nice': 2
    }
    
    # Define the direct flight graph (undirected)
    edges = [
        ('Venice','Nice'), 
        ('Naples','Amsterdam'), 
        ('Barcelona','Nice'), 
        ('Amsterdam','Nice'), 
        ('Stuttgart','Valencia'), 
        ('Stuttgart','Porto'), 
        ('Split','Stuttgart'), 
        ('Split','Naples'), 
        ('Valencia','Amsterdam'), 
        ('Barcelona','Porto'), 
        ('Valencia','Naples'), 
        ('Venice','Amsterdam'), 
        ('Barcelona','Naples'), 
        ('Barcelona','Valencia'), 
        ('Split','Amsterdam'), 
        ('Barcelona','Venice'), 
        ('Stuttgart','Amsterdam'), 
        ('Naples','Nice'), 
        ('Venice','Stuttgart'), 
        ('Split','Barcelona'), 
        ('Porto','Nice'), 
        ('Barcelona','Stuttgart'), 
        ('Venice','Naples'), 
        ('Porto','Amsterdam'), 
        ('Porto','Valencia'), 
        ('Stuttgart','Naples'), 
        ('Barcelona','Amsterdam')
    ]
    
    # Build the graph
    graph = {}
    all_cities = set(cities) | {'Nice'}
    for city in all_cities:
        graph[city] = set()
    for u, v in edges:
        graph[u].add(v)
        graph[v].add(u)
    
    # DFS function to find a valid sequence
    def dfs(sequence, next_start, remaining):
        if not remaining:
            # All non-Nice cities assigned, now assign Nice
            if next_start != 23:
                return None
            last_city = sequence[-1]
            if 'Nice' not in graph[last_city]:
                return None
            return sequence + ['Nice']
        
        # If sequence is not empty, last_city is the last in sequence; otherwise None
        last_city = sequence[-1] if sequence else None
        
        for city in list(remaining):
            # Check connection if not the first city
            if last_city is not None:
                if city not in graph[last_city]:
                    continue
            
            start = next_start
            duration = durations[city]
            end = start + duration - 1
            
            # Check constraints for specific cities
            if city == 'Venice':
                if not (start <= 10 and end >= 6):
                    continue
            elif city == 'Barcelona':
                if not (4 <= start <= 6):
                    continue
            elif city == 'Naples':
                if not (16 <= start <= 20):
                    continue
            
            # Prepare new state
            new_sequence = sequence + [city]
            new_remaining = remaining - {city}
            new_next_start = end  # next city starts at the end of the current city
            
            # Recurse
            result = dfs(new_sequence, new_next_start, new_remaining)
            if result is not None:
                return result
        
        return None
    
    # Start DFS: empty sequence, start day 1, all non-Nice cities remaining
    remaining = set(cities)
    sequence = dfs([], 1, remaining)
    
    if sequence is None:
        # Fallback: return an empty itinerary if no plan found (though constraints should yield one)
        print(json.dumps({"itinerary": []}))
        return
    
    # Compute day ranges for the itinerary
    itinerary_list = []
    current_day = 1
    for city in sequence:
        d = durations[city]
        end_day = current_day + d - 1
        day_range = f"Day {current_day}-{end_day}" if current_day != end_day else f"Day {current_day}"
        itinerary_list.append({"day_range": day_range, "place": city})
        current_day = end_day  # next city starts on the same day (travel day)
    
    # Output as JSON
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()