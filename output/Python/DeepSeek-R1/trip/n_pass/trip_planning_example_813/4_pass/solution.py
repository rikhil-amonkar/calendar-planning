import json

def main():
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
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
    
    def dfs(city, current_day, london_done, stuttgart_done, itinerary):
        key = (city, current_day, london_done, stuttgart_done)
        if key in memo:
            return memo[key]
            
        duration = duration_map[city]
        end_day = current_day + duration - 1
        if end_day > 17:
            memo[key] = None
            return None
            
        new_itinerary = itinerary + [(current_day, city, duration)]
        
        if city == 'London' and not london_done:
            if current_day in [8, 9, 10]:
                london_done = True
        if city == 'Stuttgart' and not stuttgart_done:
            if current_day in [5, 6, 7, 8, 9]:
                stuttgart_done = True
                
        if city == 'Vilnius':
            if end_day == 17 and london_done and stuttgart_done:
                return new_itinerary
            else:
                memo[key] = None
                return None
                
        next_day = end_day + 1
        for neighbor in graph.get(city, []):
            res = dfs(neighbor, next_day, london_done, stuttgart_done, new_itinerary)
            if res is not None:
                memo[key] = res
                return res
                
        memo[key] = None
        return None
        
    start_itinerary = dfs('Seville', 1, False, False, [])
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