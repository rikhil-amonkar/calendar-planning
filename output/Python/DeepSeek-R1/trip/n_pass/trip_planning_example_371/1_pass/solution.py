import json

def main():
    total_days = 9
    direct_flights = {
        'Vienna': ['Stockholm', 'Nice', 'Split'],
        'Stockholm': ['Vienna', 'Nice', 'Split'],
        'Nice': ['Vienna', 'Stockholm'],
        'Split': ['Vienna', 'Stockholm']
    }
    
    path = ['Vienna', 'Nice', 'Stockholm', 'Split']
    travel_days = [2, 3, 7]
    
    for i in range(len(path) - 1):
        current_city = path[i]
        next_city = path[i + 1]
        if next_city not in direct_flights[current_city]:
            raise ValueError(f"No direct flight from {current_city} to {next_city}")
    
    ranges = []
    ranges.append((1, travel_days[0]))
    for i in range(1, len(travel_days)):
        ranges.append((travel_days[i - 1], travel_days[i]))
    ranges.append((travel_days[-1], total_days))
    
    itinerary_list = []
    for i in range(len(path)):
        start, end = ranges[i]
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary_list.append({
            "day_range": day_range_str,
            "place": path[i]
        })
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()