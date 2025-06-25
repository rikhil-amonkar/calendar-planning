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
    
    def dfs(itinerary, next_start, visited):
        if len(visited) == 8:
            return itinerary
        
        current_city = itinerary[-1]
        
        # Check constraints for unvisited cities
        if next_start > 4 and 'Stockholm' not in visited:
            return None
        if next_start > 18 and 'Porto' not in visited:
            return None
            
        # Prioritize Stockholm first and Porto last
        candidate_cities = []
        if 'Stockholm' in graph[current_city] and 'Stockholm' not in visited:
            candidate_cities.append('Stockholm')
        for city in cities:
            if city in visited:
                continue
            if city == 'Stockholm' or city == 'Porto':
                continue
            if city in graph[current_city]:
                candidate_cities.append(city)
        if 'Porto' in graph[current_city] and 'Porto' not in visited:
            candidate_cities.append('Porto')
            
        for next_city in candidate_cities:
            duration = requirements[next_city]
            start_next = next_start
            end_next = start_next + duration - 1
            
            # Check if this city is Stockholm and includes day 4
            if next_city == 'Stockholm':
                if not (start_next <= 4 <= end_next):
                    continue
                    
            # Check if this city is Porto and includes day 18
            if next_city == 'Porto':
                if not (start_next <= 18 <= end_next):
                    continue
                    
            new_visited = visited | {next_city}
            new_itinerary = itinerary + [next_city]
            # The next city after this will start the day after this city's stay ends
            result = dfs(new_itinerary, end_next + 1, new_visited)
            if result is not None:
                return result
                
        return None
        
    # Start in Reykjavik
    start_city = 'Reykjavik'
    init_visited = {start_city}
    init_itinerary = [start_city]
    # The stay in Reykjavik ends at day 2, so next city starts at day 3
    result_itinerary = dfs(init_itinerary, 3, init_visited)
    
    if result_itinerary is None:
        print(json.dumps({"itinerary": []}))
        return
        
    # Convert to output format
    output_list = []
    current_start = 1
    for i, city in enumerate(result_itinerary):
        duration = requirements[city]
        end_day = current_start + duration - 1
        day_range_str = f"Day {current_start}-{end_day}"
        output_list.append({"day_range": day_range_str, "place": city})
        current_start = end_day + 1  # Next city starts the following day
    
    # Return to Reykjavik at the end
    final_city = 'Reykjavik'
    final_duration = requirements[final_city]
    final_start = current_start
    final_end = final_start + final_duration - 1
    
    # Ensure we end on day 21
    if final_end != 21:
        print(json.dumps({"itinerary": []}))
        return
        
    output_list.append({
        "day_range": f"Day {final_start}-{final_end}",
        "place": final_city
    })
    
    result_json = {"itinerary": output_list}
    print(json.dumps(result_json))

if __name__ == "__main__":
    main()