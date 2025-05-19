import json

def main():
    durations = {
        'Mykonos': 3,
        'Riga': 5,
        'Prague': 3,
        'Valencia': 5,
        'Zurich': 5,
        'Bucharest': 5,
        'Nice': 2
    }

    flight_connections = {
        'Mykonos': {'Nice', 'Zurich'},
        'Zurich': {'Mykonos', 'Prague', 'Riga', 'Bucharest', 'Valencia', 'Nice'},
        'Prague': {'Bucharest', 'Riga', 'Valencia', 'Zurich'},
        'Valencia': {'Bucharest', 'Zurich', 'Prague'},
        'Bucharest': {'Prague', 'Valencia', 'Riga', 'Zurich'},
        'Riga': {'Nice', 'Bucharest', 'Prague', 'Zurich'},
        'Nice': {'Mykonos', 'Zurich', 'Riga'}
    }

    itinerary_order = ['Mykonos', 'Zurich', 'Prague', 'Valencia', 'Bucharest', 'Riga', 'Nice']
    
    # Validate flight connections
    valid = True
    for i in range(len(itinerary_order) - 1):
        current = itinerary_order[i]
        next_city = itinerary_order[i+1]
        if next_city not in flight_connections.get(current, set()):
            valid = False
            break

    if not valid:
        print(json.dumps({"itinerary": []}))
        return

    # Calculate day ranges
    current_day = 1
    itinerary = []
    for city in itinerary_order:
        duration = durations[city]
        end_day = current_day + duration - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day

    # Verify constraints
    if (sum(durations.values()) - (len(itinerary_order) - 1) != 22:
        print(json.dumps({"itinerary": []}))
        return

    prague_days = next((e for e in itinerary if e['place'] == 'Prague'), None)
    mykonos_days = next((e for e in itinerary if e['place'] == 'Mykonos'), None)
    if not prague_days or prague_days['day_range'] != 'Day 7-9' or not mykonos_days or mykonos_days['day_range'] != 'Day 1-3':
        print(json.dumps({"itinerary": []}))
        return

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()