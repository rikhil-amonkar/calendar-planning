import json
from itertools import permutations

def main():
    # Define cities and direct flight connections
    cities = ['Dubrovnik', 'Frankfurt', 'Krakow']
    direct_flights = [
        frozenset({'Frankfurt', 'Krakow'}),
        frozenset({'Dubrovnik', 'Frankfurt'})
    ]
    
    # Define duration constraints for each city
    durations = {
        'Dubrovnik': 7,
        'Frankfurt': 3,
        'Krakow': 2
    }
    
    # Find valid itineraries that end in Krakow with valid transitions
    valid_orders = []
    for perm in permutations(cities):
        if perm[-1] != 'Krakow':
            continue  # Must end in Krakow for the wedding
        valid = True
        for i in range(len(perm) - 1):
            city_pair = frozenset({perm[i], perm[i+1]})
            if city_pair not in direct_flights:
                valid = False
                break
        if valid:
            valid_orders.append(perm)
    
    if not valid_orders:
        raise ValueError("No valid itinerary found")
    
    # Use the first valid order to build the itinerary
    order = valid_orders[0]
    itinerary = []
    current_day = 1
    
    for city in order:
        duration = durations[city]
        end_day = current_day + duration - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()