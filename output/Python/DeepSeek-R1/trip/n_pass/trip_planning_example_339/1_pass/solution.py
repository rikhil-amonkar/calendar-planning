import json

def main():
    total_days = 17
    days_per_city = {
        'Warsaw': 2,
        'Budapest': 7,
        'Paris': 4,
        'Riga': 7
    }
    direct_flights = {
        'Warsaw': ['Budapest', 'Riga', 'Paris'],
        'Budapest': ['Warsaw', 'Paris'],
        'Paris': ['Budapest', 'Warsaw', 'Riga'],
        'Riga': ['Warsaw', 'Paris']
    }
    wedding_start = 11
    wedding_end = 17

    # Start with Warsaw (fixed event)
    start_city = 'Warsaw'
    start_day = 1
    end_day = start_day + days_per_city[start_city] - 1
    itinerary = [{'start': start_day, 'end': end_day, 'place': start_city}]
    visited = {start_city}
    current_city = start_city
    current_end = end_day

    # DFS to find valid itinerary
    def dfs(current_city, current_end, visited, itinerary):
        if len(visited) == 4:
            if current_end == total_days:
                return itinerary
            else:
                return None
                
        for next_city in direct_flights[current_city]:
            if next_city in visited:
                continue
                
            start_next = current_end
            duration = days_per_city[next_city]
            end_next = start_next + duration - 1
            
            if end_next > total_days:
                continue
                
            if next_city == 'Riga':
                if end_next < wedding_start or start_next > wedding_end:
                    continue
                    
            new_visited = visited | {next_city}
            new_itinerary = itinerary + [{'start': start_next, 'end': end_next, 'place': next_city}]
            result = dfs(next_city, end_next, new_visited, new_itinerary)
            if result is not None:
                return result
                
        return None

    result_itinerary = dfs(current_city, current_end, visited, itinerary)
    
    if result_itinerary is None:
        print(json.dumps({"error": "No valid itinerary found"}))
        return

    # Format the itinerary for output
    output_itinerary = []
    for segment in result_itinerary:
        start = segment['start']
        end = segment['end']
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        output_itinerary.append({"day_range": day_range_str, "place": segment['place']})
    
    print(json.dumps({"itinerary": output_itinerary}))

if __name__ == "__main__":
    main()