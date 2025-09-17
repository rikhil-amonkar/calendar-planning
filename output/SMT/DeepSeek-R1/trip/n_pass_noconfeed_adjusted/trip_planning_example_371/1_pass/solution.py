from z3 import *
import json

def main():
    # Initialize solver
    solver = Solver()
    
    # Cities: Vienna=0, Stockholm=1, Nice=2, Split=3
    cities = [0, 1, 2, 3]
    city_names = {0: 'Vienna', 1: 'Stockholm', 2: 'Nice', 3: 'Split'}
    
    # Direct flights: list of pairs (city1, city2)
    direct_flights = [(0,1), (1,0), (0,2), (2,0), (0,3), (3,0), (1,3), (3,1), (1,2), (2,1)]
    
    # Variables for wake_city for days 1 to 9 (index 0 to 8)
    wake_city = [Int('wake_city_%d' % (i+1)) for i in range(9)]
    for i in range(9):
        solver.add(And(wake_city[i] >= 0, wake_city[i] <= 3))
    
    # Variables for fly for days 1 to 8 (index 0 to 7)
    fly = [Bool('fly_%d' % (i+1)) for i in range(8)]
    
    # Variables for sleep_city for days 1 to 8 (index 0 to 7)
    sleep_city = [Int('sleep_city_%d' % (i+1)) for i in range(8)]
    for i in range(8):
        solver.add(And(sleep_city[i] >= 0, sleep_city[i] <= 3))
    
    # Constraints for sleep_city and fly
    for i in range(8):
        # If not flying, sleep_city equals wake_city
        solver.add(Implies(Not(fly[i]), sleep_city[i] == wake_city[i]))
        # If flying, sleep_city != wake_city and there is a direct flight
        solver.add(Implies(fly[i], sleep_city[i] != wake_city[i]))
        # Direct flight available condition
        flight_constraints = []
        for (c1, c2) in direct_flights:
            flight_constraints.append(And(wake_city[i] == c1, sleep_city[i] == c2))
        solver.add(Implies(fly[i], Or(flight_constraints)))
    
    # Consistency: wake_city of next day equals sleep_city of current day
    for i in range(8):
        solver.add(wake_city[i+1] == sleep_city[i])
    
    # Specific constraints
    # Day 1: wake up in Vienna
    solver.add(wake_city[0] == 0)
    # Day 2: must be in Vienna (either wake up in Vienna or fly to Vienna on day2)
    solver.add(Or(wake_city[1] == 0, And(fly[1], sleep_city[1] == 0)))
    # Day 7: must be in Split
    solver.add(Or(wake_city[6] == 3, And(fly[6], sleep_city[6] == 3)))
    # Day 9: must be in Split (wake up in Split)
    solver.add(wake_city[8] == 3)
    
    # Total days constraints
    total_days = [0]*4
    for c in range(4):
        # Count wake_city days
        wake_count = Sum([If(wake_city[i] == c, 1, 0) for i in range(9)])
        # Count sleep_city days for flight days
        fly_count = Sum([If(And(fly[i], sleep_city[i] == c), 1, 0) for i in range(8)])
        total_days[c] = wake_count + fly_count
    
    solver.add(total_days[0] == 2)  # Vienna
    solver.add(total_days[1] == 5)  # Stockholm
    solver.add(total_days[2] == 2)  # Nice
    solver.add(total_days[3] == 3)  # Split
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        # Extract values
        wake_vals = [model.evaluate(wake_city[i]) for i in range(9)]
        fly_vals = [model.evaluate(fly[i]) for i in range(8)]
        sleep_vals = [model.evaluate(sleep_city[i]) for i in range(8)]
        
        # Build presence sets for each city
        presence = {0: set(), 1: set(), 2: set(), 3: set()}
        for day in range(9):
            c = wake_vals[day].as_long()
            presence[c].add(day+1)
        for day in range(8):
            if fly_vals[day]:
                c = sleep_vals[day].as_long()
                presence[c].add(day+1)
        
        # Form segments from presence sets
        segments = []
        for city, days in presence.items():
            if not days:
                continue
            sorted_days = sorted(days)
            start = sorted_days[0]
            current = start
            for d in sorted_days[1:]:
                if d == current + 1:
                    current = d
                else:
                    segments.append((start, current, city))
                    start = d
                    current = d
            segments.append((start, current, city))
        
        # Convert segments to itinerary
        itinerary = []
        for seg in segments:
            start, end, city = seg
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city_names[city]})
        
        # Sort by start day
        itinerary.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()