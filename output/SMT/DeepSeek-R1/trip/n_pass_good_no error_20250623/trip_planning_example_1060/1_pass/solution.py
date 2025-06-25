from z3 import *
import json

def main():
    # Define the cities
    City = Datatype('City')
    for city in ['Reykjavik', 'Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich']:
        City.declare(city)
    City = City.create()
    
    # Define directed flights as tuples (from, to)
    directed_flights = [
        (City.Geneva, City.Istanbul),
        (City.Istanbul, City.Geneva),
        (City.Reykjavik, City.Munich),
        (City.Munich, City.Reykjavik),
        (City.Stuttgart, City.Valencia),
        (City.Valencia, City.Stuttgart),
        (City.Reykjavik, City.Stuttgart),
        (City.Stuttgart, City.Istanbul),
        (City.Istanbul, City.Stuttgart),
        (City.Munich, City.Geneva),
        (City.Geneva, City.Munich),
        (City.Istanbul, City.Vilnius),
        (City.Vilnius, City.Istanbul),
        (City.Valencia, City.Seville),
        (City.Seville, City.Valencia),
        (City.Valencia, City.Istanbul),
        (City.Istanbul, City.Valencia),
        (City.Vilnius, City.Munich),
        (City.Seville, City.Munich),
        (City.Munich, City.Seville),
        (City.Munich, City.Istanbul),
        (City.Istanbul, City.Munich),
        (City.Valencia, City.Geneva),
        (City.Geneva, City.Valencia),
        (City.Valencia, City.Munich),
        (City.Munich, City.Valencia)
    ]
    
    # Total days
    n_days = 25
    
    # Create Z3 variables for each day
    base_city = [Const('base_city_%d' % i, City) for i in range(1, n_days+1)]
    fly = [Bool('fly_%d' % i) for i in range(1, n_days+1)]
    next_city = [Const('next_city_%d' % i, City) for i in range(1, n_days+1)]
    
    s = Solver()
    
    # Constraint: Start in Reykjavik on day 1
    s.add(base_city[0] == City.Reykjavik)
    
    # Constraints for each day
    for i in range(n_days):
        # If not flying, next_city must equal base_city
        s.add(Implies(Not(fly[i]), next_city[i] == base_city[i]))
        # If flying, next_city must be different and flight must be in directed_flights
        if i < n_days - 1:
            s.add(base_city[i+1] == next_city[i])
        s.add(Implies(fly[i], next_city[i] != base_city[i]))
        s.add(Implies(fly[i], Or([And(base_city[i] == f, next_city[i] == t) for (f, t) in directed_flights])))
    
    # Total days per city
    total_days = {}
    for city in [City.Reykjavik, City.Stuttgart, City.Istanbul, City.Vilnius, City.Seville, City.Geneva, City.Valencia, City.Munich]:
        total_days[city] = 0
        
    for i in range(n_days):
        for city in total_days.keys():
            in_city = Or(base_city[i] == city, And(fly[i], next_city[i] == city))
            total_days[city] += If(in_city, 1, 0)
    
    # Required days per city
    s.add(total_days[City.Reykjavik] == 4)
    s.add(total_days[City.Stuttgart] == 4)
    s.add(total_days[City.Istanbul] == 4)
    s.add(total_days[City.Vilnius] == 4)
    s.add(total_days[City.Seville] == 3)
    s.add(total_days[City.Geneva] == 5)
    s.add(total_days[City.Valencia] == 5)
    s.add(total_days[City.Munich] == 3)
    
    # Fixed events: must be in specific cities on specific days
    for i in [0, 1, 2, 3]:  # days 1,2,3,4 (0-indexed: 0,1,2,3)
        in_re = Or(base_city[i] == City.Reykjavik, And(fly[i], next_city[i] == City.Reykjavik))
        s.add(in_re)
    
    for i in [3, 6]:  # days 4 and 7 (0-indexed: 3 and 6)
        in_st = Or(base_city[i] == City.Stuttgart, And(fly[i], next_city[i] == City.Stuttgart))
        s.add(in_st)
        
    for i in [18, 19, 20, 21]:  # days 19,20,21,22 (0-indexed: 18,19,20,21)
        in_ist = Or(base_city[i] == City.Istanbul, And(fly[i], next_city[i] == City.Istanbul))
        s.add(in_ist)
        
    for i in [12, 13, 14]:  # days 13,14,15 (0-indexed: 12,13,14)
        in_mu = Or(base_city[i] == City.Munich, And(fly[i], next_city[i] == City.Munich))
        s.add(in_mu)
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        base_city_vals = [m.eval(base_city[i]) for i in range(n_days)]
        fly_vals = [m.eval(fly[i]) for i in range(n_days)]
        next_city_vals = [m.eval(next_city[i]) for i in range(n_days)]
        
        # Build events for output
        events = []
        current_start = 0  # 0-indexed day index
        current_city = base_city_vals[0]
        
        for i in range(n_days):
            if fly_vals[i] == True:
                if current_start <= i:
                    events.append((current_start, i, current_city))
                events.append((i, i, current_city))  # departure
                events.append((i, i, next_city_vals[i]))  # arrival
                current_city = next_city_vals[i]
                current_start = i  # next block starts at the same day (flight day)
            # If not flying, we do nothing until the flight or end
        if current_start < n_days:
            events.append((current_start, n_days-1, current_city))
        
        # Convert events to output format
        itinerary = []
        for (start, end, city) in events:
            city_name = str(city)
            if start == end:
                day_range = "Day %d" % (start+1)
            else:
                day_range = "Day %d-%d" % (start+1, end+1)
            itinerary.append({"day_range": day_range, "place": city_name})
        
        # Create the final dictionary
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()