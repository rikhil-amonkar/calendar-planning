import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich', 'Naples']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Zurich': ['Brussels', 'Nice', 'Naples', 'Copenhagen', 'Bucharest', 'Venice', 'Hamburg'],
        'Brussels': ['Zurich', 'Venice', 'Bucharest', 'Hamburg', 'Nice', 'Copenhagen', 'Naples'],
        'Bucharest': ['Copenhagen', 'Brussels', 'Hamburg', 'Naples', 'Zurich'],
        'Venice': ['Brussels', 'Naples', 'Copenhagen', 'Zurich', 'Nice', 'Hamburg'],
        'Nice': ['Zurich', 'Hamburg', 'Brussels', 'Venice', 'Naples', 'Copenhagen'],
        'Hamburg': ['Nice', 'Bucharest', 'Brussels', 'Copenhagen', 'Zurich', 'Venice', 'Salzburg'],
        'Copenhagen': ['Bucharest', 'Venice', 'Brussels', 'Zurich', 'Hamburg', 'Naples', 'Nice'],
        'Naples': ['Zurich', 'Venice', 'Bucharest', 'Brussels', 'Copenhagen', 'Nice', 'Hamburg'],
        'Salzburg': ['Hamburg']
    }
    
    # Create Z3 variables: day[i] is the city visited on day i+1 (days are 1-based)
    days = [Int(f'day_{i}') for i in range(25)]
    
    # Solver
    s = Solver()
    
    # Each day must be one of the cities (0 to 8)
    for day in days:
        s.add(And(day >= 0, day <= 8))
    
    # Duration constraints
    # Salzburg: 2 days
    s.add(Sum([If(days[i] == city_to_idx['Salzburg'], 1, 0) for i in range(25)]) == 2)
    # Venice: 5 days
    s.add(Sum([If(days[i] == city_to_idx['Venice'], 1, 0) for i in range(25)]) == 5)
    # Bucharest: 4 days
    s.add(Sum([If(days[i] == city_to_idx['Bucharest'], 1, 0) for i in range(25)]) == 4)
    # Brussels: 2 days
    s.add(Sum([If(days[i] == city_to_idx['Brussels'], 1, 0) for i in range(25)]) == 2)
    # Hamburg: 4 days
    s.add(Sum([If(days[i] == city_to_idx['Hamburg'], 1, 0) for i in range(25)]) == 4)
    # Copenhagen: 4 days
    s.add(Sum([If(days[i] == city_to_idx['Copenhagen'], 1, 0) for i in range(25)]) == 4)
    # Nice: 3 days
    s.add(Sum([If(days[i] == city_to_idx['Nice'], 1, 0) for i in range(25)]) == 3)
    # Zurich: 5 days
    s.add(Sum([If(days[i] == city_to_idx['Zurich'], 1, 0) for i in range(25)]) == 5)
    # Naples: 4 days
    s.add(Sum([If(days[i] == city_to_idx['Naples'], 1, 0) for i in range(25)]) == 4)
    
    # Specific constraints
    # Brussels between day 21 and 22 (inclusive)
    s.add(Or(
        days[20] == city_to_idx['Brussels'],  # day 21
        days[21] == city_to_idx['Brussels']   # day 22
    ))
    
    # Copenhagen between day 18 and 21 (inclusive)
    s.add(Or(
        days[17] == city_to_idx['Copenhagen'],  # day 18
        days[18] == city_to_idx['Copenhagen'],  # day 19
        days[19] == city_to_idx['Copenhagen'],  # day 20
        days[20] == city_to_idx['Copenhagen']   # day 21
    ))
    
    # Nice between day 9 and 11 (inclusive)
    s.add(Or(
        days[8] == city_to_idx['Nice'],   # day 9
        days[9] == city_to_idx['Nice'],   # day 10
        days[10] == city_to_idx['Nice']   # day 11
    ))
    
    # Naples between day 22 and 25 (inclusive)
    s.add(Or(
        days[21] == city_to_idx['Naples'],  # day 22
        days[22] == city_to_idx['Naples'],  # day 23
        days[23] == city_to_idx['Naples'],  # day 24
        days[24] == city_to_idx['Naples']   # day 25
    ))
    
    # Flight constraints: consecutive days must be the same city or connected by direct flight
    for i in range(24):
        current_city = days[i]
        next_city = days[i + 1]
        # Either stay in the same city or move to a directly connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_idx[a], next_city == city_to_idx[b]) 
              for a in direct_flights for b in direct_flights[a]]
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(25):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i + 1, 'place': cities[city_idx]})
        
        # Verify all constraints are met (sanity check)
        # (The solver should ensure this, but it's good to verify)
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        assert city_days['Salzburg'] == 2
        assert city_days['Venice'] == 5
        assert city_days['Bucharest'] == 4
        assert city_days['Brussels'] == 2
        assert city_days['Hamburg'] == 4
        assert city_days['Copenhagen'] == 4
        assert city_days['Nice'] == 3
        assert city_days['Zurich'] == 5
        assert city_days['Naples'] == 4
        
        # Specific day checks
        brussels_days = [entry['day'] for entry in itinerary if entry['place'] == 'Brussels']
        assert any(21 <= day <= 22 for day in brussels_days)
        
        copenhagen_days = [entry['day'] for entry in itinerary if entry['place'] == 'Copenhagen']
        assert any(18 <= day <= 21 for day in copenhagen_days)
        
        nice_days = [entry['day'] for entry in itinerary if entry['place'] == 'Nice']
        assert any(9 <= day <= 11 for day in nice_days)
        
        naples_days = [entry['day'] for entry in itinerary if entry['place'] == 'Naples']
        assert any(22 <= day <= 25 for day in naples_days)
        
        # Flight constraints check
        for i in range(24):
            current_place = itinerary[i]['place']
            next_place = itinerary[i + 1]['place']
            if current_place != next_place:
                assert next_place in direct_flights[current_place]
        
        # Prepare the output
        output = {
            'itinerary': itinerary
        }
        return output
    else:
        return None

# Solve and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print("No valid itinerary found.")