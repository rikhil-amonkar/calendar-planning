import itertools
import json

def main():
    total_days = 23
    required_days = {
        'Paris': 6,
        'Oslo': 5,
        'Porto': 7,
        'Geneva': 7,
        'Reykjavik': 2
    }
    
    direct_flights = {
        'Paris': ['Oslo', 'Geneva', 'Porto', 'Reykjavik'],
        'Oslo': ['Paris', 'Geneva', 'Porto', 'Reykjavik'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Geneva': ['Paris', 'Oslo', 'Porto'],
        'Reykjavik': ['Paris', 'Oslo']
    }
    
    fixed_segments = [
        {'place': 'Geneva', 'start': 1, 'end': 7},
        {'place': 'Oslo', 'start': 19, 'end': 23}
    ]
    
    middle_cities = ['Paris', 'Porto', 'Reykjavik']
    
    for perm in itertools.permutations(middle_cities):
        c2, c3, c4 = perm
        
        if (c2 in direct_flights['Geneva'] and 
            c3 in direct_flights[c2] and 
            c4 in direct_flights[c3] and 
            'Oslo' in direct_flights[c4]):
            
            D1 = required_days[c2]
            D2 = required_days[c3]
            D3 = required_days[c4]
            
            end_segment2 = 6 + D1
            end_segment3 = 5 + D1 + D2
            
            if end_segment3 <= 19:
                itinerary = [
                    {"day_range": "Day 1-7", "place": "Geneva"},
                    {"day_range": f"Day 7-{end_segment2}", "place": c2},
                    {"day_range": f"Day {end_segment2}-{end_segment3}", "place": c3},
                    {"day_range": f"Day {end_segment3}-19", "place": c4},
                    {"day_range": "Day 19-23", "place": "Oslo"}
                ]
                print(json.dumps({"itinerary": itinerary}))
                return
                
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()