from z3 import *
import json

def solve_itinerary():
    # Cities
    Prague, Berlin, Tallinn, Stockholm = Ints('Prague Berlin Tallinn Stockholm')
    cities = {
        'Prague': Prague,
        'Berlin': Berlin,
        'Tallinn': Tallinn,
        'Stockholm': Stockholm
    }
    city_list = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    
    # Direct flight connections
    direct_flights = {
        ('Berlin', 'Tallinn'),
        ('Prague', 'Tallinn'),
        ('Stockholm', 'Tallinn'),
        ('Prague', 'Stockholm'),
        ('Stockholm', 'Berlin'),
        ('Tallinn', 'Berlin'),
        ('Tallinn', 'Prague'),
        ('Tallinn', 'Stockholm'),
        ('Stockholm', 'Prague'),
        ('Berlin', 'Stockholm')
    }
    
    # Create a solver instance
    s = Solver()
    
    # Day variables: day[i] represents the city on day i+1 (since days are 1-based)
    days = [Int(f'day_{i}') for i in range(1, 13)]
    
    # Constraint: each day variable must correspond to a city (0: Prague, 1: Berlin, 2: Tallinn, 3: Stockholm)
    for day in days:
        s.add(Or([day == idx for idx, city in enumerate(city_list)]))
    
    # Total days constraints
    s.add(Sum([If(day == city_list.index('Prague'), 1, 0) for day in days]) == 2)
    s.add(Sum([If(day == city_list.index('Berlin'), 1, 0) for day in days]) == 3)
    s.add(Sum([If(day == city_list.index('Tallinn'), 1, 0) for day in days]) == 5)
    s.add(Sum([If(day == city_list.index('Stockholm'), 1, 0) for day in days]) == 5)
    
    # Specific day constraints
    # Day 6 must be Berlin
    s.add(days[5] == city_list.index('Berlin'))
    # Day 8 must be Berlin
    s.add(days[7] == city_list.index('Berlin'))
    
    # Between day 8 and day 12 (inclusive), must be in Tallinn
    for i in range(7, 12):  # days 8 to 12 (indices 7 to 11)
        s.add(days[i] == city_list.index('Tallinn'))
    
    # Flight constraints: transitions between days must be via direct flights
    for i in range(11):  # days 1-11 to days 2-12
        current_day = days[i]
        next_day = days[i+1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_day == next_day,
            Or([And(current_day == city_list.index(a), next_day == city_list.index(b)) for (a, b) in direct_flights if a != b])
        ))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(12):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = city_list[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Convert to the required JSON format
        result = {'itinerary': itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found."}, indent=2)

# Execute the function and print the result
print(solve_itinerary())