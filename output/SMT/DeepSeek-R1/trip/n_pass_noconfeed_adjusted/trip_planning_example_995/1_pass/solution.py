from z3 import *
import json

def main():
    # Define the cities
    cities = ['Barcelona', 'Brussels', 'Copenhagen', 'Oslo', 'Split', 'Stuttgart', 'Venice']
    City = Datatype('City')
    for c in cities:
        City.declare(c)
    City = City.create()
    
    # Direct flights graph
    direct_flights = [
        (City.Venice, City.Stuttgart),
        (City.Oslo, City.Brussels),
        (City.Split, City.Copenhagen),
        (City.Barcelona, City.Copenhagen),
        (City.Barcelona, City.Venice),
        (City.Brussels, City.Venice),
        (City.Barcelona, City.Stuttgart),
        (City.Copenhagen, City.Brussels),
        (City.Oslo, City.Split),
        (City.Oslo, City.Venice),
        (City.Barcelona, City.Split),
        (City.Oslo, City.Copenhagen),
        (City.Barcelona, City.Oslo),
        (City.Copenhagen, City.Stuttgart),
        (City.Split, City.Stuttgart),
        (City.Copenhagen, City.Venice),
        (City.Barcelona, City.Brussels)
    ]
    
    # Required days per city
    req_days = {
        City.Barcelona: 3,
        City.Brussels: 3,
        City.Copenhagen: 3,
        City.Oslo: 2,
        City.Split: 4,
        City.Stuttgart: 3,
        City.Venice: 4
    }
    
    num_days = 16
    s = Solver()
    
    # Variables: for each day, the city we end in (overnight stay)
    end_city = [Const(f'end_city_{i}', City) for i in range(1, num_days+1)]
    # Variables: for each day, whether we fly (change city)
    fly = [Bool(f'fly_{i}') for i in range(1, num_days+1)]
    
    # Start city is Barcelona on day 1
    s.add(end_city[0] == City.Barcelona)
    
    # Constraints for each day
    for i in range(num_days):
        if i > 0:
            # If we don't fly, end city same as previous end city
            s.add(Implies(Not(fly[i]), end_city[i] == end_city[i-1]))
            # If we fly, end city different and direct flight exists
            prev_city = end_city[i-1]
            curr_city = end_city[i]
            flight_possible = Or([And(prev_city == c1, curr_city == c2) for c1, c2 in direct_flights] +
                                [And(prev_city == c2, curr_city == c1) for c1, c2 in direct_flights])
            s.add(Implies(fly[i], flight_possible))
        else:
            # Day 1: if fly, must have direct flight from Barcelona
            flight_possible = Or([And(end_city[0] == c1, end_city[0] == c2) for c1, c2 in direct_flights if c1 == City.Barcelona or c2 == City.Barcelona])
            s.add(Implies(fly[0], flight_possible))
    
    # Total days per city (including travel days)
    for city in cities:
        city_val = getattr(City, city)
        total = 0
        for i in range(num_days):
            # Count day i+1 if we start or end in the city
            if i == 0:
                # Day 1: start in Barcelona, so count if end city is the city or start city (Barcelona) is the city
                total += If(Or(end_city[i] == city_val, City.Barcelona == city_val), 1, 0)
            else:
                # For day i+1, start city is previous end city
                total += If(Or(end_city[i] == city_val, end_city[i-1] == city_val), 1, 0)
        s.add(total == req_days[city_val])
    
    # Specific constraints
    # Barcelona must be visited on days 1-3
    for i in range(3):  # days 1,2,3
        if i == 0:
            # Day 1: already start in Barcelona
            pass
        else:
            # Day i+1: either start or end in Barcelona
            s.add(Or(end_city[i] == City.Barcelona, end_city[i-1] == City.Barcelona))
    
    # Oslo between day 3 and 4: must be in Oslo on day 3 or 4
    s.add(Or(
        Or(end_city[2] == City.Oslo, end_city[1] == City.Oslo),  # day 3: start day3=end_day2, end day3=end_city[2]
        Or(end_city[3] == City.Oslo, end_city[2] == City.Oslo)   # day 4
    ))
    
    # Brussels between day 9 and 11
    s.add(Or(
        Or(end_city[8] == City.Brussels, end_city[7] == City.Brussels),  # day 9
        Or(end_city[9] == City.Brussels, end_city[8] == City.Brussels),  # day 10
        Or(end_city[10] == City.Brussels, end_city[9] == City.Brussels) # day 11
    ))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Decode end_city for each day
        day_assignments = []
        for i in range(num_days):
            city_val = m.evaluate(end_city[i])
            city_name = None
            for c in cities:
                if city_val.eq(getattr(City, c)):
                    city_name = c
                    break
            day_assignments.append(city_name)
        
        # Group consecutive days with same city
        itinerary = []
        start_day = 1
        current_city = day_assignments[0]
        for day in range(2, num_days+1):
            if day_assignments[day-1] != current_city:
                end_day = day - 1
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": current_city})
                start_day = day
                current_city = day_assignments[day-1]
        # Add last segment
        if start_day == num_days:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{num_days}"
        itinerary.append({"day_range": day_range, "place": current_city})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()