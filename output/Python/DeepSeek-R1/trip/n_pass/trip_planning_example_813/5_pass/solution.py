import json

def main():
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    index_map = {city: idx for idx, city in enumerate(cities)}
    duration_map = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }

    edges = [
        ('Frankfurt', 'Dublin'),
        ('Frankfurt', 'London'),
        ('London', 'Dublin'),
        ('Vilnius', 'Frankfurt'),
        ('Frankfurt', 'Stuttgart'),
        ('Dublin', 'Seville'),
        ('London', 'Santorini'),
        ('Stuttgart', 'London'),
        ('Santorini', 'Dublin')
    ]
    
    graph = {}
    for u, v in edges:
        if u not in graph:
            graph[u] = []
        if v not in graph:
            graph[v] = []
        graph[u].append(v)
        graph[v].append(u)
    
    memo = {}
    
    def dfs(city, current_day, london_done, stuttgart_done, visited_mask):
        state = (city, current_day, london_done, stuttgart_done, visited_mask)
        if state in memo:
            return memo[state]
            
        idx = index_map[city]
        if visited_mask & (1 << idx):
            memo[state] = None
            return None
            
        new_visited_mask = visited_mask | (1 << idx)
        duration = duration_map[city]
        end_day = current_day + duration - 1
        if end_day > 17:
            memo[state] = None
            return None
            
        if city == 'London' and not london_done:
            stay_days = set(range(current_day, current_day + duration))
            if not (stay_days & {8, 9, 10}):
                memo[state] = None
                return None
            london_done = True
            
        if city == 'Stuttgart' and not stuttgart_done:
            stay_days = set(range(current_day, current_day + duration))
            if not (stay_days & set(range(5, 10))):
                memo[state] = None
                return None
            stuttgart_done = True
            
        if city == 'Vilnius':
            if end_day == 17 and london_done and stuttgart_done:
                result = [(current_day, city, duration)]
                memo[state] = result
                return result
            else:
                memo[state] = None
                return None
                
        next_day = end_day + 1
        for neighbor in graph[city]:
            neighbor_idx = index_map[neighbor]
            if new_visited_mask & (1 << neighbor_idx):
                continue
            suffix = dfs(neighbor, next_day, london_done, stuttgart_done, new_visited_mask)
            if suffix is not None:
                result = [(current_day, city, duration)] + suffix
                memo[state] = result
                return result
                
        memo[state] = None
        return None
        
    start_itinerary = dfs('Seville', 1, False, False, 0)
    if start_itinerary is None:
        print(json.dumps({"itinerary": []}))
        return
        
    formatted_itinerary = []
    for start, city, duration in start_itinerary:
        end_day = start + duration - 1
        if duration > 1:
            day_range = f"Day {start}-{end_day}"
        else:
            day_range = f"Day {start}"
        formatted_itinerary.append({"day_range": day_range, "place": city})
        
    print(json.dumps({"itinerary": formatted_itinerary}))

if __name__ == "__main__":
    main()