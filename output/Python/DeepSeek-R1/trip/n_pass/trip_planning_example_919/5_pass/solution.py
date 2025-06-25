import itertools
import json

def main():
    graph = {
        'Vienna': {'Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'},
        'Milan': {'Vienna', 'Riga', 'Oslo', 'Vilnius'},
        'Rome': {'Vienna', 'Oslo', 'Lisbon', 'Riga'},
        'Riga': {'Vienna', 'Milan', 'Oslo', 'Lisbon', 'Vilnius', 'Rome'},
        'Vilnius': {'Vienna', 'Milan', 'Oslo', 'Riga'},
        'Lisbon': {'Vienna', 'Riga', 'Rome', 'Oslo'},
        'Oslo': {'Riga', 'Rome', 'Vienna', 'Milan', 'Vilnius', 'Lisbon'}
    }
    
    cities = {
        'Vienna': 3,
        'Milan': 2,
        'Rome': 2,
        'Riga': 1,
        'Vilnius': 2,
        'Lisbon': 3,
        'Oslo': 2
    }
    
    middle_cities = ['Milan', 'Rome', 'Riga', 'Vilnius', 'Lisbon']
    
    for perm in itertools.permutations(middle_cities):
        seq = ['Vienna'] + list(perm) + ['Oslo']
        valid = True
        for i in range(len(seq) - 1):
            if seq[i+1] not in graph[seq[i]]:
                valid = False
                break
        if not valid:
            continue
            
        start_days = [1]
        for i in range(1, len(seq)):
            start_days.append(start_days[i-1] + cities[seq[i-1]])
        
        for idx, city in enumerate(seq):
            if city == 'Lisbon' and start_days[idx] == 9:
                itinerary = []
                for j in range(len(seq)):
                    start = start_days[j]
                    end = start + cities[seq[j]] - 1
                    day_range = f"Day {start}-{end}"
                    itinerary.append({"day_range": day_range, "place": seq[j]})
                result = {'itinerary': itinerary}
                print(json.dumps(result))
                return
                
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()