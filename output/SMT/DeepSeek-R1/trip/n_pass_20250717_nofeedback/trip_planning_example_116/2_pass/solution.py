from z3 import *
import json

def main():
    # Define the City enum
    City = Datatype('City')
    City.declare('Split')
    City.declare('Santorini')
    City.declare('London')
    City = City.create()
    
    # Create arrays for start and end cities for each day (days 1 to 18)
    days = range(1, 19)
    start = [Const(f'start_{d}', City) for d in days]
    end = [Const(f'end_{d}', City) for d in days]
    
    s = Solver()
    
    # Define allowed direct flights
    direct_flights = [
        (City.Split, City.London),
        (City.London, City.Split),
        (City.London, City.Santorini),
        (City.Santorini, City.London)
    ]
    
    # Flight constraints: if start != end, the pair must be in direct_flights
    for d in range(18):
        flight_condition = Or([And(start[d] == c1, end[d] == c2) for c1, c2 in direct_flights])
        s.add(If(start[d] != end[d], flight_condition, True))
    
    # Continuity between days: end of day d is start of day d+1
    for i in range(17):
        s.add(end[i] == start[i+1])
    
    # Conference constraints: days 12 and 18 must have Santorini at start or end
    s.add(Or(start[11] == City.Santorini, end[11] == City.Santorini))  # day 12
    s.add(Or(start[17] == City.Santorini, end[17] == City.Santorini))  # day 18
    
    # Additional constraints to guide the solver
    s.add(start[0] == City.Split)          # Start in Split on day 1
    s.add(end[17] == City.Santorini)        # End in Santorini on day 18
    
    # Count days in each city (a day counts if start or end is in the city)
    inSplit = [Or(start[i] == City.Split, end[i] == City.Split) for i in range(18)]
    inSantorini = [Or(start[i] == City.Santorini, end[i] == City.Santorini) for i in range(18)]
    inLondon = [Or(start[i] == City.London, end[i] == City.London) for i in range(18)]
    
    s.add(Sum([If(cond, 1, 0) for cond in inSplit]) == 6)
    s.add(Sum([If(cond, 1, 0) for cond in inSantorini]) == 7)
    s.add(Sum([If(cond, 1, 0) for cond in inLondon]) == 7)
    
    # Exactly 2 flight days (days where start != end)
    flight_days = [If(start[i] != end[i], 1, 0) for i in range(18)]
    s.add(Sum(flight_days) == 2)
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Map Z3 city values to strings
        city_map = {
            City.Split: "Split",
            City.Santorini: "Santorini",
            City.London: "London"
        }
        for i in range(18):
            day = i + 1
            city_val = m.evaluate(end[i], model_completion=True)
            place = city_map[city_val.as_long()]
            itinerary.append({"day": day, "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()