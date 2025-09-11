import itertools
import json

def main():
    cities = ['Reykjavik', 'Riga', 'Warsaw', 'Istanbul', 'Krakow']
    durations = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    
    graph = {
        'Istanbul': ['Krakow', 'Warsaw', 'Riga'],
        'Krakow': ['Istanbul', 'Warsaw'],
        'Reykjavik': ['Warsaw'],
        'Riga': ['Istanbul', 'Warsaw'],
        'Warsaw': ['Reykjavik', 'Istanbul', 'Krakow', 'Riga']
    }
    
    for order in itertools.permutations(cities):
        valid_order = True
        for i in range(len(order) - 1):
            if order[i+1] not in graph[order[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
            
        total_so_far = 0
        starts = [0] * len(order)
        for idx, city in enumerate(order):
            if idx == 0:
                starts[idx] = 1
            else:
                starts[idx] = 1 + total_so_far - idx
            total_so_far += durations[city]
        
        idx_riga = order.index('Riga')
        start_riga = starts[idx_riga]
        end_riga = start_riga + durations['Riga'] - 1
        if not ((start_riga <= 1 <= end_riga) or (start_riga <= 2 <= end_riga)):
            continue
            
        idx_istanbul = order.index('Istanbul')
        start_istanbul = starts[idx_istanbul]
        end_istanbul = start_istanbul + durations['Istanbul'] - 1
        if not (start_istanbul <= 7 and end_istanbul >= 2):
            continue
            
        itinerary_list = []
        for idx, city in enumerate(order):
            start = starts[idx]
            end = start + durations[city] - 1
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
        return
        
    print('{"itinerary": []}')

if __name__ == "__main__":
    main()