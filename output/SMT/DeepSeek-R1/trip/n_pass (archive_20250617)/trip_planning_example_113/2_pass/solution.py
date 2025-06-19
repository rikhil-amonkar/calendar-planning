from z3 import *

def main():
    City = Datatype('City')
    City.declare('Naples')
    City.declare('Seville')
    City.declare('Milan')
    City = City.create()
    
    days = 12
    # Arrays for day 1 to 12
    start_city = [Const(f'start_{i}', City) for i in range(1, days+1)]
    travel_day = [Bool(f'travel_{i}') for i in range(1, days+1)]
    end_city = [Const(f'end_{i}', City) for i in range(1, days+1)]
    
    s = Solver()
    
    # Direct flights only between Milan-Seville and Naples-Milan
    for i in range(days):
        s.add(If(travel_day[i],
                 Or(
                     And(start_city[i] == City.Milan, end_city[i] == City.Seville),
                     And(start_city[i] == City.Seville, end_city[i] == City.Milan),
                     And(start_city[i] == City.Naples, end_city[i] == City.Milan),
                     And(start_city[i] == City.Milan, end_city[i] == City.Naples)
                 ),
                 end_city[i] == start_city[i]
             ))
    
    # End city must match next start city
    for i in range(days-1):
        s.add(end_city[i] == start_city[i+1])
    
    # Exactly 2 travel days
    s.add(Sum([If(travel_day[i], 1, 0) for i in range(days)]) == 2)
    
    # Count days in each city
    naples_days = []
    seville_days = []
    milan_days = []
    
    for i in range(days):
        in_naples = Or(start_city[i] == City.Naples, And(travel_day[i], end_city[i] == City.Naples))
        in_seville = Or(start_city[i] == City.Seville, And(travel_day[i], end_city[i] == City.Seville))
        in_milan = Or(start_city[i] == City.Milan, And(travel_day[i], end_city[i] == City.Milan))
        naples_days.append(If(in_naples, 1, 0))
        seville_days.append(If(in_seville, 1, 0))
        milan_days.append(If(in_milan, 1, 0))
    
    s.add(Sum(naples_days) == 3)
    s.add(Sum(seville_days) == 4)
    s.add(Sum(milan_days) == 7)
    
    # Days 9-12: Must be in Seville with no travel (indices 8 to 11)
    for i in [8, 9, 10, 11]:
        s.add(travel_day[i] == False)
        s.add(start_city[i] == City.Seville)
        s.add(end_city[i] == City.Seville)
    
    if s.check() == sat:
        m = s.model()
        def city_name(city_val):
            if city_val.eq(City.Naples):
                return "Naples"
            elif city_val.eq(City.Seville):
                return "Seville"
            elif city_val.eq(City.Milan):
                return "Milan"
            else:
                return "Unknown"
        
        for i in range(days):
            day_num = i + 1
            start_val = m.eval(start_city[i])
            travel_val = m.eval(travel_day[i])
            end_val = m.eval(end_city[i])
            if is_true(travel_val):
                print(f"Day {day_num}: Travel from {city_name(start_val)} to {city_name(end_val)}")
            else:
                print(f"Day {day_num}: Stay in {city_name(start_val)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()