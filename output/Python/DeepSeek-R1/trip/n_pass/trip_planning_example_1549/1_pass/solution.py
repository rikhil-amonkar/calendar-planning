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
    
    start_sequence = ['Porto', 'Warsaw', 'Stockholm', 'Riga']
    remaining = ['Prague', 'Tallinn', 'Naples', 'Milan', 'Lisbon', 'Santorini']
    
    for perm in itertools.permutations(remaining):
        full_sequence = start_sequence + list(perm)
        valid_sequence = True
        for i in range(len(full_sequence) - 1):
            if full_sequence[i+1] not in graph[full_sequence[i]]:
                valid_sequence = False
                break
        if not valid_sequence:
            continue
            
        end_days = [0] * len(full_sequence)
        end_days[0] = city_days[full_sequence[0]]
        for i in range(1, len(full_sequence)):
            end_days[i] = end_days[i-1] + city_days[full_sequence[i]] - 1
        
        if end_days[-1] != 28:
            continue
            
        try:
            idx_tallinn = full_sequence.index('Tallinn')
            start_tallinn = 1 if idx_tallinn == 0 else end_days[idx_tallinn-1]
            end_tallinn = end_days[idx_tallinn]
            if not (start_tallinn <= 20 and end_tallinn >= 18):
                continue
                
            idx_milan = full_sequence.index('Milan')
            start_milan = 1 if idx_milan == 0 else end_days[idx_milan-1]
            end_milan = end_days[idx_milan]
            if not (start_milan <= 26 and end_milan >= 24):
                continue
                
            itinerary = []
            current_start = 1
            for i, city in enumerate(full_sequence):
                end = end_days[i]
                itinerary.append({
                    'day_range': f"Day {current_start}-{end}",
                    'place': city
                })
                current_start = end
            print(json.dumps({'itinerary': itinerary}))
            return
        except ValueError:
            continue
    print(json.dumps({'itinerary': []}))

if __name__ == "__main__":
    main()