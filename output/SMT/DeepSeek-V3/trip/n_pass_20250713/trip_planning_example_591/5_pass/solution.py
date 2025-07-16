from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Geneva', 'Munich', 'Valencia', 'Bucharest', 'Stuttgart']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    adjacency = {
        'Geneva': ['Munich', 'Valencia'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Valencia': ['Geneva', 'Munich', 'Bucharest', 'Stuttgart'],
        'Bucharest': ['Valencia', 'Munich'],
        'Stuttgart': ['Valencia']
    }
    
    num_days = 17
    s = Solver()
    
    # Variables: for each day, which city are you in?
    day_city = [Int(f'day_{i}_city') for i in range(num_days)]
    for dc in day_city:
        s.add(dc >= 0, dc < len(cities))
    
    # Constraints on consecutive days: must be the same city or adjacent
    for i in range(num_days - 1):
        current_city = day_city[i]
        next_city = day_city[i+1]
        # Transition constraint: either same city or adjacent
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_map[c1], next_city == city_map[c2])
              for c1 in adjacency for c2 in adjacency[c1]]
        ))
    
    # Duration constraints
    # Geneva: 4 days, including days 1-4 (indices 0-3)
    for i in range(4):
        s.add(day_city[i] == city_map['Geneva'])
    # Total Geneva days: 4
    geneva_days = Sum([If(day_city[i] == city_map['Geneva'], 1, 0) for i in range(num_days)])
    s.add(geneva_days == 4)
    
    # Munich: 7 days, between days 4-10 (indices 3-9)
    munich_in_period = Sum([If(And(i >=3, i <=9), 
                           If(day_city[i] == city_map['Munich'], 1, 0), 0) for i in range(num_days)])
    s.add(munich_in_period >= 1)  # At least one day in Munich during days 4-10
    # Total Munich days:7
    munich_days = Sum([If(day_city[i] == city_map['Munich'], 1, 0) for i in range(num_days)])
    s.add(munich_days ==7)
    
    # Valencia:6 days
    valencia_days = Sum([If(day_city[i] == city_map['Valencia'], 1, 0) for i in range(num_days)])
    s.add(valencia_days ==6)
    
    # Bucharest:2 days
    bucharest_days = Sum([If(day_city[i] == city_map['Bucharest'], 1, 0) for i in range(num_days)])
    s.add(bucharest_days ==2)
    
    # Stuttgart:2 days
    stuttgart_days = Sum([If(day_city[i] == city_map['Stuttgart'], 1, 0) for i in range(num_days)])
    s.add(stuttgart_days ==2)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Determine the sequence of cities
        seq = [cities[model.evaluate(day_city[i]).as_long()] for i in range(num_days)]
        
        itinerary = []
        current_place = seq[0]
        start_day = 0
        for i in range(1, num_days):
            if seq[i] != current_place:
                # Add the stay before the transition
                if start_day == i-1:
                    itinerary.append({'day_range': f'Day {start_day+1}', 'place': current_place})
                else:
                    itinerary.append({'day_range': f'Day {start_day+1}-{i}', 'place': current_place})
                # Add the transition day for departure and arrival
                itinerary.append({'day_range': f'Day {i+1}', 'place': current_place})
                itinerary.append({'day_range': f'Day {i+1}', 'place': seq[i]})
                current_place = seq[i]
                start_day = i
        # Add the last stay
        if start_day == num_days -1:
            itinerary.append({'day_range': f'Day {start_day+1}', 'place': current_place})
        else:
            itinerary.append({'day_range': f'Day {start_day+1}-{num_days}', 'place': current_place})
        
        # Verify the total days per city
        city_days = {city:0 for city in cities}
        for entry in itinerary:
            day_range = entry['day_range']
            place = entry['place']
            if '-' in day_range:
                start, end = map(int, day_range.replace('Day ', '').split('-'))
                days = end - start +1
            else:
                days = 1
            city_days[place] += days
        
        # Check against constraints
        assert city_days['Geneva'] ==4, f"Geneva days: {city_days['Geneva']}"
        assert city_days['Munich'] ==7, f"Munich days: {city_days['Munich']}"
        assert city_days['Valencia'] ==6, f"Valencia days: {city_days['Valencia']}"
        assert city_days['Bucharest'] ==2, f"Bucharest days: {city_days['Bucharest']}"
        assert city_days['Stuttgart'] ==2, f"Stuttgart days: {city_days['Stuttgart']}"
        
        # Check Geneva is days 1-4 (indices 0-3)
        assert all(seq[i] == 'Geneva' for i in range(4)), "Geneva not days 1-4"
        
        # Check Munich has at least one day between days 4-10 (indices 3-9)
        assert any(seq[i] == 'Munich' for i in range(3, 10)), "Munich not present in days 4-10"
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))