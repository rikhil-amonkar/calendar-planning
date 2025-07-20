import itertools
import json

def main():
    total_days = 17
    durations = {
        'Geneva': 4,
        'Munich': 7,
        'Bucharest': 2,
        'Valencia': 6,
        'Stuttgart': 2
    }
    
    graph = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Munich', 'Valencia'],
        'Stuttgart': ['Valencia']
    }
    
    geneva_start = 1
    geneva_end = 4
    munich_start = 4
    munich_end = 10
    
    remaining_cities = ['Bucharest', 'Valencia', 'Stuttgart']
    start_next = munich_end
    
    found = False
    valid_itinerary = None
    for perm in itertools.permutations(remaining_cities):
        A, B, C = perm
        if A not in graph['Munich']:
            continue
        if B not in graph[A]:
            continue
        if C not in graph[B]:
            continue
        
        start_A = start_next
        end_A = start_A + durations[A] - 1
        start_B = end_A
        end_B = start_B + durations[B] - 1
        start_C = end_B
        end_C = start_C + durations[C] - 1
        
        if end_C == total_days:
            found = True
            valid_itinerary = [
                {'day_range': f"Day {geneva_start}-{geneva_end}", 'place': 'Geneva'},
                {'day_range': f"Day {munich_start}-{munich_end}", 'place': 'Munich'},
                {'day_range': f"Day {start_A}-{end_A}", 'place': A},
                {'day_range': f"Day {start_B}-{end_B}", 'place': B},
                {'day_range': f"Day {start_C}-{end_C}", 'place': C}
            ]
            break
    
    if not found:
        valid_itinerary = []
    
    result = {'itinerary': valid_itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()