import json

def main():
    cities = ['Reykjavik', 'Oslo', 'Stuttgart', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Stockholm']
    requirements = {
        'Reykjavik': 2,
        'Oslo': 5,
        'Stuttgart': 5,
        'Split': 3,
        'Geneva': 2,
        'Porto': 3,
        'Tallinn': 5,
        'Stockholm': 3
    }
    
    graph = {
        'Reykjavik': {'Stuttgart', 'Stockholm', 'Tallinn', 'Oslo'},
        'Oslo': {'Reykjavik', 'Stockholm', 'Split', 'Tallinn', 'Geneva', 'Porto'},
        'Stuttgart': {'Reykjavik', 'Porto', 'Split', 'Stockholm'},
        'Split': {'Stockholm', 'Stuttgart', 'Oslo', 'Geneva'},
        'Geneva': {'Stockholm', 'Oslo', 'Split', 'Porto'},
        'Porto': {'Stuttgart', 'Oslo', 'Geneva'},
        'Tallinn': {'Oslo'},
        'Stockholm': {'Reykjavik', 'Stuttgart', 'Split', 'Geneva', 'Oslo'}
    }
    
    def dfs(itinerary, current_sum, visited):
        if len(itinerary) == 8:
            return itinerary
        
        current_city = itinerary[-1]
        for next_city in cities:
            if next_city in visited:
                continue
            if next_city not in graph[current_city]:
                continue
                
            new_sum = current_sum + (requirements[current_city] - 1)
            start_next = 1 + new_sum
            
            if next_city == 'Porto' and new_sum != 18:
                continue
            if next_city == 'Stockholm' and start_next > 4:
                continue
                
            new_visited = visited | {next_city}
            new_itinerary = itinerary + [next_city]
            result = dfs(new_itinerary, new_sum, new_visited)
            if result is not None:
                return result
                
        return None
        
    start_city = 'Reykjavik'
    init_visited = {start_city}
    init_itinerary = [start_city]
    result_itinerary = dfs(init_itinerary, 0, init_visited)
    
    if result_itinerary is None:
        print(json.dumps({"itinerary": []}))
        return
        
    output_list = []
    current_start = 1
    for i, city in enumerate(result_itinerary):
        duration = requirements[city]
        end_day = current_start + duration - 1
        day_range_str = f"Day {current_start}-{end_day}"
        output_list.append({"day_range": day_range_str, "place": city})
        if i < len(result_itinerary) - 1:
            current_start = end_day
    
    result_json = {"itinerary": output_list}
    print(json.dumps(result_json))

if __name__ == "__main__":
    main()