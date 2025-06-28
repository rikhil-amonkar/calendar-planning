import json

def main():
    total_days = 12
    cities_order = ['Prague', 'Helsinki', 'Naples', 'Frankfurt', 'Lyon']
    durations = {
        'Prague': 2,
        'Helsinki': 4,
        'Naples': 4,
        'Frankfurt': 3,
        'Lyon': 3
    }
    
    graph = {
        'Prague': ['Lyon', 'Frankfurt', 'Helsinki'],
        'Lyon': ['Prague', 'Frankfurt'],
        'Frankfurt': ['Prague', 'Lyon', 'Helsinki', 'Naples'],
        'Helsinki': ['Prague', 'Frankfurt', 'Naples'],
        'Naples': ['Helsinki', 'Frankfurt']
    }
    
    for i in range(len(cities_order) - 1):
        current_city = cities_order[i]
        next_city = cities_order[i + 1]
        if next_city not in graph[current_city]:
            raise ValueError(f"No direct flight from {current_city} to {next_city}")
    
    current_start = 1
    itinerary_list = []
    for city in cities_order:
        dur = durations[city]
        current_end = current_start + dur - 1
        if current_end > total_days:
            raise ValueError("Total days exceeded")
        itinerary_list.append({
            "day_range": f"Day {current_start}-{current_end}",
            "place": city
        })
        current_start = current_end
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()