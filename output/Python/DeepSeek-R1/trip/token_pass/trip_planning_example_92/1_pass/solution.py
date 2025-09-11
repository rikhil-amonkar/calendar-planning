import json

def main():
    total_days = 12
    required_days = {
        'Riga': 5,
        'Vilnius': 7,
        'Dublin': 2
    }
    
    routes = [
        ['Dublin', 'Riga', 'Vilnius'],
        ['Vilnius', 'Riga', 'Dublin']
    ]
    
    itinerary = []
    for route in routes:
        A, B, C = route
        try:
            x = required_days[A]
            y = x + required_days[B] - 1
            if y < x or y > total_days:
                continue
            if required_days[C] == total_days - y + 1:
                itinerary = [
                    {"day_range": f"Day 1-{x}", "place": A},
                    {"day_range": f"Day {x}-{y}", "place": B},
                    {"day_range": f"Day {y}-{total_days}", "place": C}
                ]
                break
        except KeyError:
            continue
            
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()