import json

def main():
    total_days = 13
    stays = {
        "Seville": 2,
        "Stuttgart": 7,
        "Porto": 3,
        "Madrid": 4
    }
    stuttgart_conference_days = [7, 13]
    madrid_min_day = 1
    madrid_max_day = 4
    graph = {
        "Porto": ["Stuttgart", "Seville", "Madrid"],
        "Seville": ["Porto", "Madrid"],
        "Madrid": ["Porto", "Seville"],
        "Stuttgart": ["Porto"]
    }
    
    segments = []
    
    start_madrid = 1
    end_madrid = start_madrid + stays["Madrid"] - 1
    segments.append((start_madrid, end_madrid, "Madrid"))
    
    current_city = "Madrid"
    current_end = end_madrid
    next_city = "Seville"
    if next_city in graph[current_city]:
        start_next = current_end
        end_next = start_next + stays[next_city] - 1
        segments.append((start_next, end_next, next_city))
        current_city = next_city
        current_end = end_next
    else:
        next_city = "Porto"
        if next_city in graph[current_city]:
            start_next = current_end
            end_next = start_next + stays[next_city] - 1
            segments.append((start_next, end_next, next_city))
            current_city = next_city
            current_end = end_next
    
    if current_city == "Seville":
        next_city = "Porto"
        if next_city in graph[current_city]:
            start_next = current_end
            end_next = start_next + stays[next_city] - 1
            segments.append((start_next, end_next, next_city))
            current_city = next_city
            current_end = end_next
    elif current_city == "Porto":
        next_city = "Seville"
        if next_city in graph[current_city]:
            start_next = current_end
            end_next = start_next + stays[next_city] - 1
            segments.append((start_next, end_next, next_city))
            current_city = next_city
            current_end = end_next
    
    if current_city in graph:
        next_city = "Stuttgart"
        if next_city in graph[current_city]:
            start_next = current_end
            end_next = start_next + stays[next_city] - 1
            if end_next <= total_days:
                segments.append((start_next, end_next, next_city))
    
    itinerary_list = []
    for seg in segments:
        start, end, city = seg
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()