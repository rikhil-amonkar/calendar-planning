from z3 import *

def main():
    # Define the City datatype
    City = Datatype('City')
    City.declare('Brussels')
    City.declare('Barcelona')
    City.declare('Split')
    City = City.create()
    
    # Arrays for base_city (for days 1 to 13) and travel (for days 1 to 12)
    base_city = [ Const('base_city_%d' % i, City) for i in range(1, 14) ]
    travel = [ Bool('travel_%d' % i) for i in range(1, 13) ]
    
    s = Solver()
    
    # Constraint: Start in Brussels on day 1
    s.add(base_city[0] == City.Brussels)
    
    # Function to check adjacency
    def adjacent(c1, c2):
        return Or(
            And(c1 == City.Brussels, c2 == City.Barcelona),
            And(c1 == City.Barcelona, c2 == City.Brussels),
            And(c1 == City.Barcelona, c2 == City.Split),
            And(c1 == City.Split, c2 == City.Barcelona)
        )
    
    # Constraints for each day from 1 to 12
    for i in range(0, 12):  # i from 0 to 11 for base_city indices 0 to 11 (days 1 to 12)
        # If traveling on day i+1, then base_city[i] and base_city[i+1] must be adjacent and different
        # Otherwise, base_city[i+1] must be the same as base_city[i]
        s.add(
            If(travel[i],
               And(base_city[i] != base_city[i+1], adjacent(base_city[i], base_city[i+1])),
               base_city[i+1] == base_city[i]
            )
        )
    
    # Define in_city for each day and city
    in_Brussels = [ Or(base_city[i] == City.Brussels, 
                    And(travel[i], base_city[i+1] == City.Brussels)) 
                  for i in range(0, 12) ]
    in_Barcelona = [ Or(base_city[i] == City.Barcelona, 
                     And(travel[i], base_city[i+1] == City.Barcelona)) 
                   for i in range(0, 12) ]
    in_Split = [ Or(base_city[i] == City.Split, 
                 And(travel[i], base_city[i+1] == City.Split)) 
               for i in range(0, 12) ]
    
    # Total days in each city must be 2, 7, 5 respectively
    s.add(Sum([If(cond, 1, 0) for cond in in_Brussels]) == 2)
    s.add(Sum([If(cond, 1, 0) for cond in in_Barcelona]) == 7)
    s.add(Sum([If(cond, 1, 0) for cond in in_Split]) == 5)
    
    # Exactly two travel days
    s.add(Sum([If(travel[i], 1, 0) for i in range(0,12)]) == 2)
    
    # Additional constraints: must be in Brussels on day1 and day2
    s.add(in_Brussels[0] == True)   # Day1
    s.add(in_Brussels[1] == True)   # Day2
    
    # Check the model
    if s.check() == sat:
        m = s.model()
        # Evaluate base_city and travel
        base_city_vals = []
        for i in range(0, 13):
            val = m[base_city[i]]
            base_city_vals.append(val)
        
        travel_vals = []
        for i in range(0, 12):
            val = m[travel[i]]
            travel_vals.append(val)
        
        # Convert Z3 values to strings
        city_names = { 
            City.Brussels: "Brussels", 
            City.Barcelona: "Barcelona", 
            City.Split: "Split" 
        }
        base_city_str = [ city_names[base_city_vals[i]] for i in range(0,13) ]
        travel_bool = [ is_true(travel_vals[i]) for i in range(0,12) ]
        
        # Build the itinerary
        itinerary = []
        flight_days = []  # list of tuples: (day, from_city, to_city)
        
        # Record flight days
        for day in range(1, 13):  # day from 1 to 12
            if travel_bool[day-1]:
                from_city = base_city_str[day-1]  # base_city at start of day
                to_city = base_city_str[day]       # base_city at start of next day (arrival city)
                flight_days.append( (day, from_city, to_city) )
        
        # Build contiguous blocks
        blocks = []
        start_day = 1
        current_city = base_city_str[0]
        for day in range(1, 13):  # current day from 1 to 12
            if day < 12 and travel_bool[day-1]:
                blocks.append( (start_day, day, current_city) )
                start_day = day
                current_city = base_city_str[day]   # because base_city for day+1 is set for the next block starting at 'day'
            elif day == 12:
                blocks.append( (start_day, day, current_city) )
        
        # Add blocks to itinerary
        for (s, e, city) in blocks:
            if s == e:
                day_range = f"Day {s}"
            else:
                day_range = f"Day {s}-{e}"
            itinerary.append( {"day_range": day_range, "place": city} )
        
        # Add flight day records: for each flight day, add departure and arrival
        for (day, from_city, to_city) in flight_days:
            itinerary.append( {"day_range": f"Day {day}", "place": from_city} )
            itinerary.append( {"day_range": f"Day {day}", "place": to_city} )
        
        # Output as JSON-like dictionary
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()