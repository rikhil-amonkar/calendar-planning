import json
from itertools import permutations

def main():
    total_days = 11
    city_days = {
        'Seville': 6,
        'Paris': 2,
        'Krakow': 5
    }
    workshop_city = 'Krakow'
    workshop_start = 1
    workshop_end = 5
    direct_flights = {
        'Krakow': ['Paris'],
        'Paris': ['Krakow', 'Seville'],
        'Seville': ['Paris']
    }
    
    cities = list(city_days.keys())
    perms = permutations(cities)
    solutions = []
    
    for perm in perms:
        valid_route = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in direct_flights[perm[i]]:
                valid_route = False
                break
        if not valid_route:
            continue
            
        A, B, C = perm
        a = city_days[A]
        b = a + city_days[B] - 1
        if a < 1 or b < a or b > total_days:
            continue
        c_days = total_days - b + 1
        if c_days != city_days[C]:
            continue
        
        if workshop_city == A:
            block_idx = 0
        elif workshop_city == B:
            block_idx = 1
        elif workshop_city == C:
            block_idx = 2
        else:
            continue
            
        if block_idx == 0:
            safe = True
        elif block_idx == 1:
            safe = (a <= workshop_end)
        else:
            safe = (b <= workshop_end)
        
        if not safe:
            continue
        
        itinerary = [
            {'day_range': f"Day 1-{a}", 'place': A},
            {'day_range': f"Day {a}-{b}", 'place': B},
            {'day_range': f"Day {b}-{total_days}", 'place': C}
        ]
        solutions.append(itinerary)
        break
    
    if solutions:
        result = {'itinerary': solutions[0]}
    else:
        result = {'itinerary': []}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()