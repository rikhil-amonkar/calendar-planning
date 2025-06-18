from z3 import *
import json

def main():
    # Define the cities
    cities = ['Vienna', 'Prague', 'Split', 'Stockholm', 'Brussels', 'Riga', 'Munich', 'Seville', 'Istanbul', 'Amsterdam']
    
    # Define the direct flights as a list of tuples
    direct_flights_list = [
        ('Riga', 'Stockholm'), ('Stockholm', 'Brussels'), ('Istanbul', 'Munich'), ('Istanbul', 'Riga'),
        ('Prague', 'Split'), ('Vienna', 'Brussels'), ('Vienna', 'Riga'), ('Split', 'Stockholm'),
        ('Munich', 'Amsterdam'), ('Split', 'Amsterdam'), ('Amsterdam', 'Stockholm'), ('Amsterdam', 'Riga'),
        ('Vienna', 'Stockholm'), ('Vienna', 'Istanbul'), ('Vienna', 'Seville'), ('Istanbul', 'Amsterdam'),
        ('Munich', 'Brussels'), ('Prague', 'Munich'), ('Riga', 'Munich'), ('Prague', 'Amsterdam'),
        ('Prague', 'Brussels'), ('Prague', 'Istanbul'), ('Istanbul', 'Stockholm'), ('Vienna', 'Prague'),
        ('Munich', 'Split'), ('Vienna', 'Amsterdam'), ('Prague', 'Stockholm'), ('Brussels', 'Seville'),
        ('Munich', 'Stockholm'), ('Istanbul', 'Brussels'), ('Amsterdam', 'Seville'), ('Vienna', 'Split'),
        ('Munich', 'Seville'), ('Riga', 'Brussels'), ('Prague', 'Riga'), ('Vienna', 'Munich')
    ]
    
    # Create a set of direct flight pairs (undirected, sorted)
    direct_pairs = set()
    for u, v in direct_flights_list:
        direct_pairs.add((min(u, v), max(u, v)))
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables: in_city[city, day] for each city and day (1 to 20)
    in_city = {}
    for city in cities:
        for d in range(1, 21):
            in_city[(city, d)] = Bool('in_%s_%d' % (city, d))
    
    # Create flight_day variables for each day (1 to 20)
    flight_day = {}
    for d in range(1, 21):
        flight_day[d] = Bool('flight_%d' % d)
    
    # Fixed constraints
    # Vienna: days 1-5
    for d in [1,2,3,4,5]:
        s.add(in_city[('Vienna', d)] == True)
    # Prague: days 5-9
    for d in [5,6,7,8,9]:
        s.add(in_city[('Prague', d)] == True)
    # Split: days 11-13
    for d in [11,12,13]:
        s.add(in_city[('Split', d)] == True)
    # Stockholm: days 16-17
    for d in [16,17]:
        s.add(in_city[('Stockholm', d)] == True)
    # Riga: must be in Riga on at least one of day 15 or 16
    s.add(Or(in_city[('Riga',15)], in_city[('Riga',16)]))
    
    # Total days per city
    total_days = {
        'Vienna': 5,
        'Prague': 5,
        'Split': 3,
        'Stockholm': 2,
        'Brussels': 2,
        'Riga': 2,
        'Munich': 2,
        'Seville': 3,
        'Istanbul': 2,
        'Amsterdam': 3
    }
    for city in cities:
        s.add(Sum([If(in_city[(city, d)], 1, 0) for d in range(1,21)]) == total_days[city])
    
    # Flight days: total must be 9
    s.add(Sum([If(flight_day[d], 1, 0) for d in range(1,21)]) == 9)
    
    # Constraints for each day: number of cities and direct flights
    for d in range(1,21):
        # List of variables for this day
        vars_d = [in_city[(c, d)] for c in cities]
        # Sum of cities on day d must be 1 + (1 if flight_day[d] else 0)
        s.add(Sum([If(v,1,0) for v in vars_d]) == 1 + If(flight_day[d], 1, 0))
        
        # For every pair of distinct cities, if they are both present and not connected, it's invalid
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                if (min(c1,c2), max(c1,c2)) not in direct_pairs:
                    s.add(Not(And(in_city[(c1,d)], in_city[(c2,d)]))
    
    # Continuity constraints: for each city and each day transition
    for d in range(1,20):
        for city in cities:
            # If in city on day d and not on day d+1, then flight on day d+1 must occur and we are in city on day d+1 (departure)
            s.add(Implies(
                And(in_city[(city, d)], Not(in_city[(city, d+1)])),
                And(flight_day[d+1], in_city[(city, d+1)])
            ))
            # If not in city on day d and in city on day d+1, then flight on day d+1 must occur and we are in city on day d+1 (arrival)
            s.add(Implies(
                And(Not(in_city[(city, d)]), in_city[(city, d+1)]),
                And(flight_day[d+1], in_city[(city, d+1)])
            ))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        # Prepare the itinerary output
        itinerary = []
        
        # First, add contiguous blocks
        for city in cities:
            days_in_city = [d for d in range(1,21) if m.evaluate(in_city[(city, d)]) == True]
            if not days_in_city:
                continue
            # Find contiguous intervals
            intervals = []
            start = days_in_city[0]
            end = days_in_city[0]
            for i in range(1, len(days_in_city)):
                if days_in_city[i] == end + 1:
                    end = days_in_city[i]
                else:
                    intervals.append((start, end))
                    start = days_in_city[i]
                    end = days_in_city[i]
            intervals.append((start, end))
            
            for (start, end) in intervals:
                if start == end:
                    itinerary.append({"day_range": "Day %d" % start, "place": city})
                else:
                    itinerary.append({"day_range": "Day %d-%d" % (start, end), "place": city})
        
        # Then, add singleton records for each city for each flight day it is in
        for d in range(1,21):
            for city in cities:
                if m.evaluate(in_city[(city, d)]) == True:
                    itinerary.append({"day_range": "Day %d" % d, "place": city})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()