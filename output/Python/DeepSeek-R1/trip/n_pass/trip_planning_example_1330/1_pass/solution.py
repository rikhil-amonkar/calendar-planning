import itertools
import json

def main():
    direct_flights = [
        ("Zurich", "Brussels"),
        ("Bucharest", "Copenhagen"),
        ("Venice", "Brussels"),
        ("Nice", "Zurich"),
        ("Hamburg", "Nice"),
        ("Zurich", "Naples"),
        ("Hamburg", "Bucharest"),
        ("Zurich", "Copenhagen"),
        ("Bucharest", "Brussels"),
        ("Hamburg", "Brussels"),
        ("Venice", "Naples"),
        ("Venice", "Copenhagen"),
        ("Bucharest", "Naples"),
        ("Hamburg", "Copenhagen"),
        ("Venice", "Zurich"),
        ("Nice", "Brussels"),
        ("Hamburg", "Venice"),
        ("Copenhagen", "Naples"),
        ("Nice", "Naples"),
        ("Hamburg", "Zurich"),
        ("Salzburg", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Brussels", "Naples"),
        ("Copenhagen", "Brussels"),
        ("Venice", "Nice"),
        ("Nice", "Copenhagen")
    ]
    
    graph = set()
    for a, b in direct_flights:
        graph.add((a, b))
        graph.add((b, a))
    
    days = {
        'Salzburg': 2,
        'Venice': 5,
        'Bucharest': 4,
        'Hamburg': 4,
        'Copenhagen': 4,
        'Nice': 3,
        'Zurich': 5,
        'Brussels': 2,
        'Naples': 4
    }
    
    cities_list = ['Salzburg', 'Venice', 'Bucharest', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich']
    candidates_last = ['Zurich', 'Venice', 'Bucharest', 'Hamburg', 'Copenhagen']
    
    found = False
    valid_perm = None
    s_values = None
    
    for perm in itertools.permutations(cities_list):
        if perm[6] not in candidates_last:
            continue
        if (perm[6], 'Brussels') not in graph:
            continue
        
        valid_order = True
        for i in range(6):
            if (perm[i], perm[i+1]) not in graph:
                valid_order = False
                break
        if not valid_order:
            continue
        
        s = [0] * 7
        s[0] = 1
        for i in range(1, 7):
            s[i] = s[i-1] + days[perm[i-1]] - 1
        
        nice_index = perm.index('Nice')
        s_nice = s[nice_index]
        if not (7 <= s_nice <= 11):
            continue
        
        cop_index = perm.index('Copenhagen')
        s_cop = s[cop_index]
        if s_cop < 15 or s_cop > 21:
            continue
        if s_cop + 3 > 21:
            continue
        
        found = True
        valid_perm = perm
        s_values = s
        break
    
    if not found:
        print('{"itinerary": []}')
        return
    
    itinerary = []
    for i in range(7):
        city = valid_perm[i]
        start = s_values[i]
        end = start + days[city] - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    itinerary.append({"day_range": "Day 21-22", "place": "Brussels"})
    itinerary.append({"day_range": "Day 22-25", "place": "Naples"})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()