from z3 import *
import json

def main():
    # Cities and their indices
    cities = ['Nice', 'Dublin', 'Krakow', 'Lyon', 'Frankfurt']
    c_index = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    days = 20
    
    # Direct flights as unordered pairs
    edges = [
        (c_index['Nice'], c_index['Dublin']),
        (c_index['Dublin'], c_index['Frankfurt']),
        (c_index['Dublin'], c_index['Krakow']),
        (c_index['Krakow'], c_index['Frankfurt']),
        (c_index['Lyon'], c_index['Frankfurt']),
        (c_index['Nice'], c_index['Frankfurt']),
        (c_index['Lyon'], c_index['Dublin']),
        (c_index['Nice'], c_index['Lyon'])
    ]
    
    solver = Solver()
    
    # city_end[0] to city_end[20], where city_end[d] is the city at the end of day d
    city_end = [Int(f'city_end_{d}') for d in range(0, days+1)]
    
    # Fix start and end cities
    solver.add(city_end[0] == c_index['Nice'])
    solver.add(city_end[days] == c_index['Frankfurt'])
    
    # Each city_end must be between 0 and 4
    for d in range(1, days+1):
        solver.add(city_end[d] >= 0, city_end[d] < n_cities)
    
    # Flight constraints: if city changes, must be connected by a direct flight
    for d in range(1, days+1):
        a = city_end[d-1]
        b = city_end[d]
        solver.add(If(a != b, 
                     Or([And(a == i, b == j) for (i, j) in edges] + 
                        [And(a == j, b == i) for (i, j) in edges]), 
                     True))
    
    # in_city[d][c] indicates presence in city c on day d (1-indexed)
    in_city = [[Bool(f'in_city_{d}_{c}') for c in range(n_cities)] for d in range(1, days+1)]
    
    # Define in_city based on city_end
    for d in range(1, days+1):
        for c in range(n_cities):
            solver.add(in_city[d-1][c] == Or(
                city_end[d] == c,
                And(city_end[d-1] == c, city_end[d] != c)
            ))
    
    # Constraints for Nice: must be present on days 1-5, absent otherwise
    for d in range(1, days+1):
        if 1 <= d <= 5:
            solver.add(in_city[d-1][c_index['Nice']] == True)
        else:
            solver.add(in_city[d-1][c_index['Nice']] == False)
    
    # Constraints for Frankfurt: must be present on days 19-20, absent otherwise
    for d in range(1, days+1):
        if 19 <= d <= 20:
            solver.add(in_city[d-1][c_index['Frankfurt']] == True)
        else:
            solver.add(in_city[d-1][c_index['Frankfurt']] == False)
    
    # Total days constraints for other cities
    dublin_days = Sum([If(in_city[d][c_index['Dublin']], 1, 0) for d in range(0, days)])
    krakow_days = Sum([If(in_city[d][c_index['Krakow']], 1, 0) for d in range(0, days)])
    lyon_days = Sum([If(in_city[d][c_index['Lyon']], 1, 0) for d in range(0, days)])
    
    solver.add(dublin_days == 7)
    solver.add(krakow_days == 6)
    solver.add(lyon_days == 4)
    
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        current_start = 1
        current_city = m.evaluate(city_end[0]).as_long()
        
        for d in range(1, days+1):
            curr_city_val = m.evaluate(city_end[d]).as_long()
            if curr_city_val != current_city:
                itinerary.append({
                    'day_range': f'Day {current_start}-{d-1}',
                    'place': cities[current_city]
                })
                itinerary.append({
                    'day_range': f'Day {d}-{d}',
                    'place': f'{cities[current_city]} and {cities[curr_city_val]}'
                })
                current_start = d+1
                current_city = curr_city_val
        
        if current_start <= days:
            itinerary.append({
                'day_range': f'Day {current_start}-{days}',
                'place': cities[current_city]
            })
        
        print(json.dumps({'itinerary': itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()