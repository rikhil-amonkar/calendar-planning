from z3 import *
import json

def main():
    # Define city constants as integers
    Split = 0
    Santorini = 1
    London = 2
    n_days = 18
    
    # Create start and end city variables for each day
    start = [Int(f'start_{d}') for d in range(1, n_days+1)]
    end = [Int(f'end_{d}') for d in range(1, n_days+1)]
    
    s = Solver()
    
    # Constraint: cities must be integers 0, 1, or 2
    for i in range(n_days):
        s.add(And(start[i] >= 0, start[i] <= 2))
        s.add(And(end[i] >= 0, end[i] <= 2))
    
    # Define allowed direct flights
    direct_flights = [
        (Split, London),
        (London, Split),
        (London, Santorini),
        (Santorini, London)
    ]
    
    # Flight constraints: if start != end, must be a valid flight
    for i in range(n_days):
        flight_cond = Or([And(start[i] == c1, end[i] == c2) for c1, c2 in direct_flights])
        s.add(If(start[i] != end[i], flight_cond, True))
    
    # Continuity between days
    for i in range(n_days - 1):
        s.add(end[i] == start[i+1])
    
    # Conference constraints
    s.add(Or(start[11] == Santorini, end[11] == Santorini))  # Day 12
    s.add(Or(start[17] == Santorini, end[17] == Santorini))  # Day 18
    
    # Start and end constraints
    s.add(start[0] == Split)          # Start in Split on day 1
    s.add(end[17] == Santorini)        # End in Santorini on day 18
    
    # Count days in each city
    inSplit = [Or(start[i] == Split, end[i] == Split) for i in range(n_days)]
    inSantorini = [Or(start[i] == Santorini, end[i] == Santorini) for i in range(n_days)]
    inLondon = [Or(start[i] == London, end[i] == London) for i in range(n_days)]
    
    s.add(Sum([If(cond, 1, 0) for cond in inSplit]) == 6)
    s.add(Sum([If(cond, 1, 0) for cond in inSantorini]) == 7)
    s.add(Sum([If(cond, 1, 0) for cond in inLondon]) == 7)
    
    # Exactly 2 flight days
    flight_days = [If(start[i] != end[i], 1, 0) for i in range(n_days)]
    s.add(Sum(flight_days) == 2)
    
    # Solve and output itinerary
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = {Split: "Split", Santorini: "Santorini", London: "London"}
        for i in range(n_days):
            day = i + 1
            city_val = m.evaluate(end[i]).as_long()
            itinerary.append({"day": day, "place": city_names[city_val]})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()