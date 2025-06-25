import itertools
import json

def main():
    city_days = {
        'Prague': 5,
        'Tallinn': 3,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 5,
        'Milan': 3,
        'Lisbon': 5,
        'Santorini': 5,
        'Riga': 4,
        'Stockholm': 2
    }
    
    graph = {
        'Riga': ['Prague', 'Milan', 'Warsaw', 'Stockholm', 'Tallinn', 'Lisbon'],
        'Stockholm': ['Milan', 'Lisbon', 'Riga', 'Warsaw', 'Prague', 'Tallinn', 'Santorini'],
        'Milan': ['Stockholm', 'Riga', 'Naples', 'Porto', 'Prague', 'Lisbon', 'Warsaw', 'Santorini'],
        'Lisbon': ['Stockholm', 'Warsaw', 'Naples', 'Porto', 'Prague', 'Milan', 'Riga'],
        'Warsaw': ['Naples', 'Lisbon', 'Stockholm', 'Riga', 'Porto', 'Tallinn', 'Prague', 'Milan'],
        'Naples': ['Warsaw', 'Milan', 'Lisbon', 'Santorini'],
        'Porto': ['Lisbon', 'Milan', 'Warsaw'],
        'Prague': ['Riga', 'Tallinn', 'Stockholm', 'Warsaw', 'Lisbon', 'Milan'],
        'Tallinn': ['Riga', 'Prague', 'Warsaw', 'Stockholm'],
        'Santorini': ['Stockholm', 'Milan', 'Naples']
    }
    
    start_city = 'Porto'
    end_city = 'Santorini'
    mandatory = ['Tallinn', 'Milan']
    other_cities = [city for city in city_days.keys() if city != start_city and city != end_city and city not in mandatory]
    days_map_other = {city: city_days[city] for city in other_cities}
    target = 14  # 28 total days - 3 (Porto) - 3 (Tallinn) - 3 (Milan) - 5 (Santorini) = 14 days

    valid_subsets = []
    for size in range(1, len(other_cities) + 1):
        for subset in itertools.combinations(other_cities, size):
            if sum(days_map_other[city] for city in subset) == target:
                valid_subsets.append(subset)
    
    for subset in valid_subsets:
        cities_to_permute = list(subset) + mandatory
        for perm in itertools.permutations(cities_to_permute):
            sequence = [start_city] + list(perm) + [end_city]
            valid_path = True
            for i in range(len(sequence) - 1):
                if sequence[i+1] not in graph[sequence[i]]:
                    valid_path = False
                    break
            if not valid_path:
                continue
            
            current = 1
            day_ranges = []
            for city in sequence:
                start = current
                end = start + city_days[city] - 1
                current = end + 1
                day_ranges.append((start, end, city))
            
            if current - 1 != 28:
                continue
            
            tallinn_ok = False
            milan_ok = False
            for (start, end, city) in day_ranges:
                if city == 'Tallinn':
                    if start >= 18 and end <= 20:
                        tallinn_ok = True
                if city == 'Milan':
                    if start >= 24 and end <= 26:
                        milan_ok = True
            
            if tallinn_ok and milan_ok:
                itinerary = []
                for (start, end, city) in day_ranges:
                    itinerary.append({
                        'day_range': f"Day {start}-{end}",
                        'place': city
                    })
                print(json.dumps({'itinerary': itinerary}, indent=2))
                return
    
    print(json.dumps({'itinerary': []}, indent=2))

if __name__ == "__main__":
    main()