import itertools
import json

def main():
    cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
    required = {
        'Krakow': 5,
        'Frankfurt': 4,
        'Oslo': 3,
        'Dubrovnik': 5,
        'Naples': 5
    }
    connections_list = [
        ('Dubrovnik', 'Oslo'),
        ('Frankfurt', 'Krakow'),
        ('Frankfurt', 'Oslo'),
        ('Dubrovnik', 'Frankfurt'),
        ('Krakow', 'Oslo'),
        ('Naples', 'Oslo'),
        ('Naples', 'Dubrovnik'),
        ('Naples', 'Frankfurt')
    ]
    connections_set = set()
    for conn in connections_list:
        sorted_conn = tuple(sorted(conn))
        connections_set.add(sorted_conn)
    
    for perm in itertools.permutations(cities):
        c0, c1, c2, c3, c4 = perm
        a0 = required[c0]
        a1 = required[c1]
        a2 = required[c2]
        a3 = required[c3]
        a4 = required[c4]
        
        a = a0
        b = a + a1 - 1
        c = b + a2 - 1
        d = c + a3 - 1
        if d != 19 - a4:
            continue
        
        oslo_index = perm.index('Oslo')
        if oslo_index == 0:
            if a < 16:
                continue
        elif oslo_index == 1:
            if a > 18 or b < 16:
                continue
        elif oslo_index == 2:
            if b > 18 or c < 16:
                continue
        elif oslo_index == 3:
            if c > 18 or d < 16:
                continue
        
        dubrovnik_index = perm.index('Dubrovnik')
        if dubrovnik_index == 1:
            if a > 9:
                continue
        elif dubrovnik_index == 2:
            if b > 9:
                continue
        elif dubrovnik_index == 3:
            if c > 9:
                continue
        elif dubrovnik_index == 4:
            if d > 9:
                continue
        
        conn01 = tuple(sorted([c0, c1]))
        if conn01 not in connections_set:
            continue
        conn12 = tuple(sorted([c1, c2]))
        if conn12 not in connections_set:
            continue
        conn23 = tuple(sorted([c2, c3]))
        if conn23 not in connections_set:
            continue
        conn34 = tuple(sorted([c3, c4]))
        if conn34 not in connections_set:
            continue
        
        itinerary = [
            {"day_range": f"Day 1-{a}", "place": c0},
            {"day_range": f"Day {a}-{b}", "place": c1},
            {"day_range": f"Day {b}-{c}", "place": c2},
            {"day_range": f"Day {c}-{d}", "place": c3},
            {"day_range": f"Day {d}-18", "place": c4}
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        return
    
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()