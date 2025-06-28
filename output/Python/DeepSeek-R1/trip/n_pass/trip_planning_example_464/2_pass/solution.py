import json

def main():
    cities_order = ['Krakow', 'Frankfurt', 'Dubrovnik', 'Naples', 'Oslo']
    required = {
        'Krakow': 5,
        'Frankfurt': 4,
        'Dubrovnik': 5,
        'Naples': 5,
        'Oslo': 3
    }
    
    a0 = required[cities_order[0]]
    a1 = required[cities_order[1]]
    a2 = required[cities_order[2]]
    a3 = required[cities_order[3]]
    a4 = required[cities_order[4]]
    
    a = a0
    b = a + a1 - 1
    c = b + a2 - 1
    d = c + a3 - 1
    
    itinerary = [
        {"day_range": f"Day 1-{a}", "place": cities_order[0]},
        {"day_range": f"Day {a}-{b}", "place": cities_order[1]},
        {"day_range": f"Day {b}-{c}", "place": cities_order[2]},
        {"day_range": f"Day {c}-{d}", "place": cities_order[3]},
        {"day_range": f"Day {d}-18", "place": cities_order[4]}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()