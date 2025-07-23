from z3 import *

def solve_itinerary():
    # Cities and their codes
    cities = {
        'Berlin': 0,
        'Nice': 1,
        'Athens': 2,
        'Stockholm': 3,
        'Barcelona': 4,
        'Vilnius': 5,
        'Lyon': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights as adjacency list
    direct_flights = {
        0: [1, 2, 3, 4, 5],  # Berlin
        1: [0, 2, 3, 4, 6],   # Nice
        2: [0, 1, 3, 4, 5],   # Athens
        3: [0, 1, 2, 4],       # Stockholm
        4: [0, 1, 2, 3, 6],    # Barcelona
        5: [0, 2],             # Vilnius
        6: [1, 4]              # Lyon
    }
    
    # Create solver with increased timeout
    s = Solver()
    s.set("timeout", 60000)  # 60 seconds timeout
    
    # Variables: day[i] is the city on day i+1 (since days are 1-based)
    days = [Int(f'day_{i}') for i in range(20)]
    
    # Each day must be a valid city code (0 to 6)
    for day in days:
        s.add(day >= 0, day <= 6)
    
    # Must start in Berlin on day 1
    s.add(days[0] == cities['Berlin'])
    
    # Berlin constraints: conferences on day 1 and day 3
    s.add(days[0] == cities['Berlin'])
    s.add(days[2] == cities['Berlin'])
    
    # Barcelona workshop between day 3 and day 4
    # Must be in Barcelona on either day 3 or 4
    s.add(Or(days[2] == cities['Barcelona'], days[3] == cities['Barcelona']))
    
    # Lyon wedding between day 4 and day 5
    # Must be in Lyon on either day 4 or 5
    s.add(Or(days[3] == cities['Lyon'], days[4] == cities['Lyon']))
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for i in range(19):
        current = days[i]
        next_day = days[i+1]
        
        # Create OR condition for all possible transitions
        transition_constraints = [current == next_day]  # Stay in same city
        
        for src in direct_flights:
            for dest in direct_flights[src]:
                transition_constraints.append(And(current == src, next_day == dest))
        
        s.add(Or(transition_constraints))
    
    # Total days per city constraints
    def count_days(city_code):
        return Sum([If(days[i] == city_code, 1, 0) for i in range(20)])
    
    s.add(count_days(cities['Berlin']) == 3)
    s.add(count_days(cities['Nice']) == 5)
    s.add(count_days(cities['Athens']) == 5)
    s.add(count_days(cities['Stockholm']) == 5)
    s.add(count_days(cities['Barcelona']) == 2)
    s.add(count_days(cities['Vilnius']) == 4)
    s.add(count_days(cities['Lyon']) == 2)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            city_code = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'place': city_names[city_code]})
        
        # Verify all constraints are satisfied
        total_days = {city: 0 for city in cities}
        for entry in itinerary:
            total_days[entry['place']] += 1
        
        # Convert to the required JSON format
        result = {'itinerary': itinerary}
        return result
    else:
        print("Failed to find solution. Reason:", s.reason_unknown())
        return None

# Execute the solver and print the result
result = solve_itinerary()
if result:
    print(result)
else:
    print("No solution found.")