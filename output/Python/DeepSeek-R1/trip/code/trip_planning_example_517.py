import json

def main():
    direct_flights = {
        'Bucharest': ['Warsaw', 'Copenhagen'],
        'Warsaw': ['Copenhagen', 'Stuttgart', 'Bucharest'],
        'Stuttgart': ['Copenhagen', 'Warsaw'],
        'Copenhagen': ['Warsaw', 'Stuttgart', 'Bucharest', 'Dubrovnik'],
        'Dubrovnik': ['Copenhagen']
    }
    
    itinerary_steps = [
        ('Bucharest', 1, 6),
        ('Warsaw', 6, 7),
        ('Stuttgart', 7, 13),
        ('Copenhagen', 13, 15),
        ('Dubrovnik', 15, 19)
    ]
    
    valid = True
    for i in range(1, len(itinerary_steps)):
        prev = itinerary_steps[i-1][0]
        curr = itinerary_steps[i][0]
        if curr not in direct_flights.get(prev, []):
            valid = False
            break
    
    days_met = {
        'Bucharest': 6,
        'Warsaw': 2,
        'Stuttgart': 7,
        'Copenhagen': 3,
        'Dubrovnik': 5
    }
    days_count = {city: 0 for city in days_met}
    for city, start, end in itinerary_steps:
        days_count[city] += end - start + 1
    
    for city, req in days_met.items():
        if days_count.get(city, 0) < req:
            valid = False
    
    if not valid:
        print(json.dumps({"itinerary": []}))
        return
    
    itinerary = []
    for step in itinerary_steps:
        city, s, e = step
        dr = f"Day {s}-{e}" if s != e else f"Day {s}"
        itinerary.append({"day_range": dr, "place": city})
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()