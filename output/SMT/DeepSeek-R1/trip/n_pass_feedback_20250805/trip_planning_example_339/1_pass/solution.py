from z3 import *

def main():
    # Define the City enum
    City = Datatype('City')
    City.declare('Warsaw')
    City.declare('Budapest')
    City.declare('Paris')
    City.declare('Riga')
    City = City.create()
    
    # Connections (direct flights)
    connections = [
        (City.Warsaw, City.Budapest),
        (City.Budapest, City.Warsaw),
        (City.Warsaw, City.Riga),
        (City.Riga, City.Warsaw),
        (City.Warsaw, City.Paris),
        (City.Paris, City.Warsaw),
        (City.Budapest, City.Paris),
        (City.Paris, City.Budapest),
        (City.Paris, City.Riga),
        (City.Riga, City.Paris)
    ]
    
    # Create solver
    s = Solver()
    
    # Create variables for each day (1 to 17)
    c = [ Const('c_' + str(i+1), City) for i in range(17) ]
    
    # Constraints for days 1 and 2: must be Warsaw
    s.add(c[0] == City.Warsaw)
    s.add(c[1] == City.Warsaw)
    
    # Constraints for consecutive days: if different, must be connected by a direct flight
    for i in range(16):  # from day1 to day16, because we look at day i and i+1
        current = c[i]
        next_city = c[i+1]
        # If they are the same, no flight needed
        # If different, must be in connections
        constraint = Or(current == next_city, 
                        Or([ And(current == a, next_city == b) for (a, b) in connections ]))
        s.add(constraint)
    
    # Counters for each city (shown days + hidden days from travel)
    count_Warsaw   = 0
    count_Budapest = 0
    count_Paris    = 0
    count_Riga     = 0
    
    # Count shown days
    for i in range(17):
        count_Warsaw   = count_Warsaw   + If(c[i] == City.Warsaw, 1, 0)
        count_Budapest = count_Budapest + If(c[i] == City.Budapest, 1, 0)
        count_Paris    = count_Paris    + If(c[i] == City.Paris, 1, 0)
        count_Riga     = count_Riga     + If(c[i] == City.Riga, 1, 0)
    
    # Count hidden days (from travel days: next city gets an extra count on the travel day)
    for i in range(16):  # travels between day i (1-based: i+1) and day i+1 (1-based: i+2)
        count_Warsaw   = count_Warsaw   + If(And(c[i] != c[i+1], c[i+1] == City.Warsaw), 1, 0)
        count_Budapest = count_Budapest + If(And(c[i] != c[i+1], c[i+1] == City.Budapest), 1, 0)
        count_Paris    = count_Paris    + If(And(c[i] != c[i+1], c[i+1] == City.Paris), 1, 0)
        count_Riga     = count_Riga     + If(And(c[i] != c[i+1], c[i+1] == City.Riga), 1, 0)
    
    # Add constraints for total days per city
    s.add(count_Warsaw == 2)
    s.add(count_Budapest == 7)
    s.add(count_Paris == 4)
    s.add(count_Riga == 7)
    
    # Constraint: at least one shown day in Riga between day11 and day17 (inclusive)
    # In our array, day11 is index 10, day17 is index 16
    s.add(Or([ c[i] == City.Riga for i in range(10, 17) ]))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        # Map the Z3 enum to string
        city_names = {
            City.Warsaw: "Warsaw",
            City.Budapest: "Budapest",
            City.Paris: "Paris",
            City.Riga: "Riga"
        }
        for i in range(17):
            day = i+1
            city_val = model.eval(c[i])
            city_name = city_names[city_val]
            itinerary_list.append({"day": day, "city": city_name})
        
        # Output as JSON dictionary
        result = {
            "itinerary": itinerary_list
        }
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()