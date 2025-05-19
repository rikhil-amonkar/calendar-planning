import json

def main():
    days_in_city = {
        'Paris': 6,
        'Madrid': 7,
        'Bucharest': 2,
        'Seville': 3
    }
    
    flight_connections = {
        'Paris': ['Bucharest', 'Seville', 'Madrid'],
        'Bucharest': ['Paris', 'Madrid'],
        'Madrid': ['Paris', 'Seville', 'Bucharest'],
        'Seville': ['Paris', 'Madrid']
    }
    
    itinerary = []
    itinerary.append({'place': 'Madrid', 'start_day': 1, 'end_day': 7})
    
    current_city = 'Madrid'
    next_city = 'Seville'
    if next_city not in flight_connections[current_city]:
        raise ValueError("Invalid flight connection")
    start = 7
    end = start + days_in_city[next_city] - 1
    itinerary.append({'place': next_city, 'start_day': start, 'end_day': end})
    
    current_city = next_city
    next_city = 'Paris'
    if next_city not in flight_connections[current_city]:
        raise ValueError("Invalid flight connection")
    start = end
    end = start + days_in_city[next_city] - 1
    itinerary.append({'place': next_city, 'start_day': start, 'end_day': end})
    
    current_city = next_city
    next_city = 'Bucharest'
    if next_city not in flight_connections[current_city]:
        raise ValueError("Invalid flight connection")
    start = end
    end = start + days_in_city[next_city] - 1
    itinerary.append({'place': next_city, 'start_day': start, 'end_day': end})
    
    formatted = []
    for seg in itinerary:
        s = seg['start_day']
        e = seg['end_day']
        dr = f"Day {s}" if s == e else f"Day {s}-{e}"
        formatted.append({'day_range': dr, 'place': seg['place']})
    
    print(json.dumps({'itinerary': formatted}))

if __name__ == "__main__":
    main()