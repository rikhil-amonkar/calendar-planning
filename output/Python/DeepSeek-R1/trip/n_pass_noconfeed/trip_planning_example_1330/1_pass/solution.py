import itertools
import json

def main():
    cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich', 'Naples']
    durations = {
        'Salzburg': 2,
        'Venice': 5,
        'Bucharest': 4,
        'Brussels': 2,
        'Hamburg': 4,
        'Copenhagen': 4,
        'Nice': 3,
        'Zurich': 5,
        'Naples': 4
    }
    
    flights = [
        ('Zurich', 'Brussels'),
        ('Bucharest', 'Copenhagen'),
        ('Venice', 'Brussels'),
        ('Nice', 'Zurich'),
        ('Hamburg', 'Nice'),
        ('Zurich', 'Naples'),
        ('Hamburg', 'Bucharest'),
        ('Zurich', 'Copenhagen'),
        ('Bucharest', 'Brussels'),
        ('Hamburg', 'Brussels'),
        ('Venice', 'Naples'),
        ('Venice', 'Copenhagen'),
        ('Bucharest', 'Naples'),
        ('Hamburg', 'Copenhagen'),
        ('Venice', 'Zurich'),
        ('Nice', 'Brussels'),
        ('Hamburg', 'Venice'),
        ('Copenhagen', 'Naples'),
        ('Nice', 'Naples'),
        ('Hamburg', 'Zurich'),
        ('Salzburg', 'Hamburg'),
        ('Zurich', 'Bucharest'),
        ('Brussels', 'Naples'),
        ('Copenhagen', 'Brussels'),
        ('Venice', 'Nice'),
        ('Nice', 'Copenhagen')
    ]
    
    flight_set = set()
    for a, b in flights:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    for perm in itertools.permutations(cities):
        valid = True
        for i in range(8):
            if (perm[i], perm[i+1]) not in flight_set:
                valid = False
                break
        if not valid:
            continue
        
        s = [0] * 9
        e = [0] * 9
        s[0] = 1
        e[0] = s[0] + durations[perm[0]] - 1
        
        for i in range(1, 9):
            s[i] = s[i-1] + durations[perm[i-1]] - 1
            e[i] = s[i] + durations[perm[i]] - 1
        
        if e[8] != 25:
            continue
        
        try:
            idx_brussels = perm.index('Brussels')
        except ValueError:
            valid = False
            continue
        
        if s[idx_brussels] != 21:
            continue
        
        idx_copenhagen = perm.index('Copenhagen')
        if not (s[idx_copenhagen] <= 21 and e[idx_copenhagen] >= 18):
            continue
        
        idx_nice = perm.index('Nice')
        if not (s[idx_nice] <= 11 and e[idx_nice] >= 9):
            continue
        
        idx_naples = perm.index('Naples')
        if not (s[idx_naples] <= 25 and e[idx_naples] >= 22):
            continue
        
        itinerary = []
        for i in range(9):
            start = s[i]
            end = e[i]
            day_range_str = f"Day {start}-{end}" if start != end else f"Day {start}"
            itinerary.append({"day_range": day_range_str, "place": perm[i]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        return
    
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()