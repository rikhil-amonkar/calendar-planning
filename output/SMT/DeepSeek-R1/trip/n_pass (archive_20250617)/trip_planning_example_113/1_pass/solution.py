from z3 import *

def main():
    # Define the City datatype
    City = Datatype('City')
    City.declare('Naples')
    City.declare('Seville')
    City.declare('Milan')
    City = City.create()
    
    # Arrays for the variables for each day (1 to 12)
    city_start = [None] + [Const(f'city_start_{i}', City) for i in range(1, 13)]
    travel = [None] + [Bool(f'travel_{i}') for i in range(1, 13)]
    city_end = [None] + [Const(f'city_end_{i}', City) for i in range(1, 13)]
    
    s = Solver()
    
    # Constraint: For each day, if traveling, the start and end must be connected by a direct flight; otherwise, end equals start.
    for i in range(1, 13):
        s.add(If(travel[i],
                 Or(
                     And(city_start[i] == City.Milan, city_end[i] == City.Seville),
                     And(city_start[i] == City.Seville, city_end[i] == City.Milan),
                     And(city_start[i] == City.Naples, city_end[i] == City.Milan),
                     And(city_start[i] == City.Milan, city_end[i] == City.Naples)
                 ),
                 city_end[i] == city_start[i]
             ))
    
    # Constraint: The end city of day i must be the start city of day i+1 for days 1-11.
    for i in range(1, 12):
        s.add(city_start[i+1] == city_end[i])
    
    # Constraint: Exactly 2 travel days.
    s.add(Sum([If(travel[i], 1, 0) for i in range(1, 13)]) == 2)
    
    # Expressions for counting days in each city
    n_days = []  # Naples days
    s_days = []  # Seville days
    m_days = []  # Milan days
    
    for i in range(1, 13):
        # On day i, we are in the start city. If traveling, we are also in the end city.
        in_naples = If(Or(city_start[i] == City.Naples, 
                          And(travel[i], city_end[i] == City.Naples)), 1, 0)
        in_seville = If(Or(city_start[i] == City.Seville, 
                           And(travel[i], city_end[i] == City.Seville)), 1, 0)
        in_milan = If(Or(city_start[i] == City.Milan, 
                         And(travel[i], city_end[i] == City.Milan)), 1, 0)
        n_days.append(in_naples)
        s_days.append(in_seville)
        m_days.append(in_milan)
    
    # Constraint: Total days in each city
    s.add(Sum(n_days) == 3)
    s.add(Sum(s_days) == 4)
    s.add(Sum(m_days) == 7)
    
    # Constraint: Days 9 to 12 must be in Seville (index 8 to 11 in zero-based list)
    for idx in [8, 9, 10, 11]:
        s.add(s_days[idx] == 1)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Helper function to convert Z3 constant to string
        def city_str(val):
            if val.eq(City.Naples):
                return "Naples"
            elif val.eq(City.Seville):
                return "Seville"
            elif val.eq(City.Milan):
                return "Milan"
            else:
                return "Unknown"
        
        # Output the travel plan
        for i in range(1, 13):
            start_val = m[city_start[i]]
            travel_val = m[travel[i]]
            end_val = m[city_end[i]]
            if is_true(travel_val):
                print(f"Day {i}: Travel from {city_str(start_val)} to {city_str(end_val)}")
            else:
                print(f"Day {i}: Stay in {city_str(start_val)}")
    else:
        print("No solution")

if __name__ == '__main__':
    main()