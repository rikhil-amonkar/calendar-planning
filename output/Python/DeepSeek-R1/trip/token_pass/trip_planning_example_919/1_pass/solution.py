import itertools
import json

def main():
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    days_req = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Lisbon': 3,
        'Vilnius': 4,
        'Oslo': 3
    }
    
    graph = {city: {} for city in cities}
    
    bidirectional_edges = [
        ('Riga', 'Oslo'),
        ('Rome', 'Oslo'),
        ('Vienna', 'Milan'),
        ('Vienna', 'Vilnius'),
        ('Vienna', 'Lisbon'),
        ('Riga', 'Milan'),
        ('Lisbon', 'Oslo'),
        ('Rome', 'Lisbon'),
        ('Vienna', 'Riga'),
        ('Vienna', 'Rome'),
        ('Milan', 'Oslo'),
        ('Vienna', 'Oslo'),
        ('Vilnius', 'Oslo'),
        ('Vilnius', 'Milan'),
        ('Riga', 'Lisbon'),
        ('Milan', 'Lisbon')
    ]
    
    directed_edges = [
        ('Rome', 'Riga'),
        ('Riga', 'Vilnius')
    ]
    
    for a, b in bidirectional_edges:
        graph[a][b] = True
        graph[b][a] = True
        
    for a, b in directed_edges:
        graph[a][b] = True
        
    for perm in itertools.permutations(cities):
        start = [0] * 7
        end = [0] * 7
        start[0] = 1
        end[0] = start[0] + days_req[perm[0]] - 1
        for i in range(1, 7):
            start[i] = end[i-1]
            end[i] = start[i] + days_req[perm[i]] - 1
            
        if end[6] != 15:
            continue
            
        vienna_index = None
        for i, city in enumerate(perm):
            if city == 'Vienna':
                vienna_index = i
                break
        if vienna_index is None:
            continue
        if not (start[vienna_index] <= 1 <= end[vienna_index] and start[vienna_index] <= 4 <= end[vienna_index]):
            continue
            
        lisbon_index = None
        for i, city in enumerate(perm):
            if city == 'Lisbon':
                lisbon_index = i
                break
        if lisbon_index is None:
            continue
        found_lisbon = False
        for d in range(11, 14):
            if start[lisbon_index] <= d <= end[lisbon_index]:
                found_lisbon = True
                break
        if not found_lisbon:
            continue
            
        oslo_index = None
        for i, city in enumerate(perm):
            if city == 'Oslo':
                oslo_index = i
                break
        if oslo_index is None:
            continue
        found_oslo = False
        for d in range(13, 16):
            if start[oslo_index] <= d <= end[oslo_index]:
                found_oslo = True
                break
        if not found_oslo:
            continue
            
        valid_flights = True
        for i in range(6):
            from_city = perm[i]
            to_city = perm[i+1]
            if to_city not in graph[from_city] or not graph[from_city][to_city]:
                valid_flights = False
                break
                
        if valid_flights:
            itinerary = []
            for i in range(7):
                itinerary.append({
                    "day_range": f"Day {start[i]}-{end[i]}",
                    "place": perm[i]
                })
            result = {"itinerary": itinerary}
            print(json.dumps(result))
            return
            
    print('{"itinerary": []}')

if __name__ == '__main__':
    main()