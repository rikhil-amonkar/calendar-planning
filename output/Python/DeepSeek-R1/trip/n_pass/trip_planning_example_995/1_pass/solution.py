import json

def main():
    direct_flight_pairs = [
        ('Venice', 'Stuttgart'),
        ('Oslo', 'Brussels'),
        ('Split', 'Copenhagen'),
        ('Barcelona', 'Copenhagen'),
        ('Barcelona', 'Venice'),
        ('Brussels', 'Venice'),
        ('Barcelona', 'Stuttgart'),
        ('Copenhagen', 'Brussels'),
        ('Oslo', 'Split'),
        ('Oslo', 'Venice'),
        ('Barcelona', 'Split'),
        ('Oslo', 'Copenhagen'),
        ('Barcelona', 'Oslo'),
        ('Copenhagen', 'Stuttgart'),
        ('Split', 'Stuttgart'),
        ('Copenhagen', 'Venice'),
        ('Barcelona', 'Brussels')
    ]
    
    graph = {}
    for a, b in direct_flight_pairs:
        if a not in graph:
            graph[a] = set()
        graph[a].add(b)
        if b not in graph:
            graph[b] = set()
        graph[b].add(a)
    
    days_required = {
        'Barcelona': 3,
        'Oslo': 2,
        'Split': 4,
        'Copenhagen': 3,
        'Brussels': 3,
        'Venice': 4,
        'Stuttgart': 3
    }
    
    order = ['Barcelona', 'Oslo', 'Split', 'Copenhagen', 'Brussels', 'Venice', 'Stuttgart']
    
    itinerary_blocks = []
    start = 1
    for city in order:
        end = start + days_required[city] - 1
        itinerary_blocks.append((start, end, city))
        start = end
    
    valid = True
    for i in range(len(order) - 1):
        if order[i+1] not in graph.get(order[i], set()):
            valid = False
            break
    
    if itinerary_blocks[0][0] != 1 or itinerary_blocks[0][1] != 3:
        valid = False
    
    if itinerary_blocks[1][0] != 3 or itinerary_blocks[1][1] != 4:
        valid = False
    
    brussels_block = itinerary_blocks[4]
    brussels_start, brussels_end = brussels_block[0], brussels_block[1]
    if not (brussels_start <= 9 <= brussels_end or brussels_start <= 10 <= brussels_end or brussels_start <= 11 <= brussels_end):
        valid = False
    
    if not valid:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for block in itinerary_blocks:
            s, e, city = block
            day_range_str = f"Day {s}-{e}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
        result = {"itinerary": itinerary_list}
    
    print(json.dumps(result))

if __name__ == '__main__':
    main()