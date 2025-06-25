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
    other_cities = [city for city in city_days.keys() if city != start_city and city != end_city]
    
    for perm in itertools.permutations(other_cities):
        sequence = [start_city] + list(perm) + [end_city]
        valid_sequence = True
        for i in range(len(sequence) - 1):
            if sequence[i+1] not in graph[sequence[i]]:
                valid_sequence = False
                break
        if not valid_sequence:
            continue
        
        current_end = 0
        day_ranges = []
        for city in sequence:
            start_day = current_end + 1
            end_day = start_day + city_days[city] - 1
            current_end = end_day
            day_ranges.append((start_day, end_day))
        
        idx_tallinn = sequence.index('Tallinn')
        start_t, end_t = day_ranges[idx_tallinn]
        if not (start_t <= 20 and end_t >= 18):
            continue
        
        idx_milan = sequence.index('Milan')
        start_m, end_m = day_ranges[idx_milan]
        if not (start_m <= 26 and end_m >= 24):
            continue
        
        itinerary = []
        for i in range(len(sequence)):
            s, e = day_ranges[i]
            itinerary.append({
                'day_range': f"Day {s}-{e}",
                'place': sequence[i]
            })
        
        print(json.dumps({'itinerary': itinerary}, indent=2))
        return
    
    print(json.dumps({'itinerary': []}, indent=2))

if __name__ == "__main__":
    main()