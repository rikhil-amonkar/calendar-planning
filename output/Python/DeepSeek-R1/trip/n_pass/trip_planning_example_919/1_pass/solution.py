import itertools
import json

def main():
    graph = {
        'Vienna': {'Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'},
        'Milan': {'Vienna', 'Riga', 'Oslo', 'Vilnius'},
        'Rome': {'Vienna', 'Oslo', 'Lisbon', 'Riga'},
        'Riga': {'Vienna', 'Milan', 'Oslo', 'Lisbon', 'Vilnius'},
        'Vilnius': {'Vienna', 'Milan', 'Oslo'},
        'Lisbon': {'Vienna', 'Riga', 'Rome', 'Oslo'},
        'Oslo': {'Riga', 'Rome', 'Vienna', 'Milan', 'Vilnius', 'Lisbon'}
    }
    
    cities = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Vilnius': 4,
        'Lisbon': 3,
        'Oslo': 3
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
            
        s = [0] * 7
        s[0] = 1
        for i in range(1, 7):
            s[i] = s[i-1] + cities[seq[i-1]] - 1
        
        for idx in range(1, 6):
            if seq[idx] == 'Lisbon':
                if 9 <= s[idx] <= 13:
                    itinerary = []
                    for j in range(7):
                        start_day = s[j]
                        end_day = s[j] + cities[seq[j]] - 1
                        day_range = f"Day {start_day}-{end_day}"
                        itinerary.append({"day_range": day_range, "place": seq[j]})
                    result = {'itinerary': itinerary}
                    print(json.dumps(result))
                    return
                    
    print('{"itinerary": []}')

if __name__ == "__main__":
    main()