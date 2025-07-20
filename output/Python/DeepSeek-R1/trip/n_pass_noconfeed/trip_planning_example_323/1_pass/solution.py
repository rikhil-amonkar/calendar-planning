import json

def main():
    total_days = 16
    fixed_split_start = 7
    fixed_split_end = 11
    days_per_city = {
        'London': 7,
        'Split': 5,
        'Oslo': 2,
        'Porto': 5
    }
    direct_flights_list = [('London', 'Oslo'), ('Split', 'Oslo'), ('Oslo', 'Porto'), ('London', 'Split')]
    
    graph = {}
    for a, b in direct_flights_list:
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set()).add(a)
    
    segments = []
    segments.append((1, 7, 'London'))
    segments.append((fixed_split_start, fixed_split_end, 'Split'))
    
    visited_cities = {'London', 'Split'}
    remaining_cities = set(['Oslo', 'Porto'])
    
    next_city = None
    split_neighbors = graph.get('Split', set())
    for city in split_neighbors:
        if city in remaining_cities:
            next_city = city
            break
    if next_city is None:
        next_city = 'Oslo'
    
    segments.append((11, 12, next_city))
    visited_cities.add(next_city)
    remaining_cities.remove(next_city)
    
    next_after = remaining_cities.pop()
    segments.append((12, 16, next_after))
    
    itinerary_list = []
    for start, end, city in segments:
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()