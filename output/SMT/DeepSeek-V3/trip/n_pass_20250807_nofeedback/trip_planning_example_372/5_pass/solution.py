from z3 import *

def solve_itinerary():
    # Cities mapping
    Madrid, Seville, Porto, Stuttgart = 0, 1, 2, 3
    cities = ['Madrid', 'Seville', 'Porto', 'Stuttgart']
    
    # Direct flights (bidirectional)
    direct_flights = {
        Madrid: [Seville, Porto],
        Seville: [Madrid, Porto],
        Porto: [Madrid, Seville, Stuttgart],
        Stuttgart: [Porto]
    }
    
    s = Solver()
    
    # Day variables (1-13)
    days = [Int(f'day_{i}') for i in range(1, 14)]
    
    # Each day must be a valid city
    for day in days:
        s.add(Or([day == c for c in [Madrid, Seville, Porto, Stuttgart]]))
    
    # Flight transition constraints
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == Madrid, Or(next_day == Seville, next_day == Porto)),
            And(current == Seville, Or(next_day == Madrid, next_day == Porto)),
            And(current == Porto, Or(next_day == Madrid, next_day == Seville, next_day == Stuttgart)),
            And(current == Stuttgart, next_day == Porto)
        ))
    
    # Total days per city
    s.add(Sum([If(d == Madrid, 1, 0) for d in days]) == 4)
    s.add(Sum([If(d == Seville, 1, 0) for d in days]) == 2)
    s.add(Sum([If(d == Porto, 1, 0) for d in days]) == 3)
    s.add(Sum([If(d == Stuttgart, 1, 0) for d in days]) == 7)
    
    # Conference days in Stuttgart
    s.add(days[6] == Stuttgart)  # Day 7
    s.add(days[12] == Stuttgart)  # Day 13
    
    # Madrid visit between days 1-4 (must be at least one day)
    s.add(Or([days[i] == Madrid for i in range(4)]))
    
    # Additional constraints to help the solver:
    # 1. Madrid must be visited for at least 2 consecutive days
    # 2. Seville must be visited for exactly 2 consecutive days
    # 3. Porto must be visited for at least 1 day before Stuttgart
    
    # Madrid consecutive days
    for i in range(len(days)-1):
        s.add(Implies(
            And(days[i] == Madrid, days[i+1] != Madrid),
            Sum([If(d == Madrid, 1, 0) for d in days[i+1:]]) == 0
        ))
    
    # Seville consecutive days
    s.add(Or(
        And(days[0] == Seville, days[1] == Seville),
        And(days[1] == Seville, days[2] == Seville),
        # ... similar for other positions
        And(days[11] == Seville, days[12] == Seville)
    ))
    
    # Porto before Stuttgart
    for i in range(len(days)):
        s.add(Implies(
            days[i] == Stuttgart,
            Or([days[j] == Porto for j in range(i)])
        ))
    
    # Solve and return itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = [{'day': i+1, 'place': cities[m.evaluate(days[i]).as_long()]} 
                   for i in range(13)]
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

print(solve_itinerary())