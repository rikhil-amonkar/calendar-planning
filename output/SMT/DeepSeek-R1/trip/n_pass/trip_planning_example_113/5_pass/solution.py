from z3 import *

def main():
    City = Datatype('City')
    City.declare('Naples')
    City.declare('Seville')
    City.declare('Milan')
    City = City.create()
    
    days = 12
    start_city = [Const(f'start_{i}', City) for i in range(days)]
    travel_day = [Bool(f'travel_{i}') for i in range(days)]
    end_city = [Const(f'end_{i}', City) for i in range(days)]
    
    s = Solver()
    
    s.add(start_city[0] == City.Naples)
    
    for i in range(days):
        s.add(
            If(travel_day[i],
                Or(
                    And(start_city[i] == City.Milan, end_city[i] == City.Seville),
                    And(start_city[i] == City.Seville, end_city[i] == City.Milan),
                    And(start_city[i] == City.Naples, end_city[i] == City.Milan),
                    And(start_city[i] == City.Milan, end_city[i] == City.Naples)
                ),
                end_city[i] == start_city[i]
            )
        )
    
    for i in range(days - 1):
        s.add(end_city[i] == start_city[i+1])
    
    s.add(Sum([If(travel_day[i], 1, 0) for i in range(days)]) == 2)
    
    s.add(end_city[8] == City.Seville)
    for i in range(9, 12):
        s.add(travel_day[i] == False)
        s.add(start_city[i] == City.Seville)
        s.add(end_city[i] == City.Seville)
    
    naples_count = 0
    seville_count = 0
    milan_count = 0
    
    for i in range(days):
        naples_count += If(Or(start_city[i] == City.Naples, And(travel_day[i], start_city[i] == City.Naples)), 1, 0)
        seville_count += If(Or(start_city[i] == City.Seville, And(travel_day[i], end_city[i] == City.Seville)), 1, 0)
        milan_count += If(Or(start_city[i] == City.Milan, And(travel_day[i], Or(start_city[i] == City.Milan, end_city[i] == City.Milan))), 1, 0)
    
    s.add(naples_count == 3, seville_count == 4, milan_count == 7)
    
    if s.check() == sat:
        m = s.model()
        city_names = {
            City.Naples: "Naples",
            City.Seville: "Seville",
            City.Milan: "Milan"
        }
        for i in range(days):
            day = i + 1
            start_val = m.eval(start_city[i])
            travel_val = m.eval(travel_day[i])
            end_val = m.eval(end_city[i])
            if is_true(travel_val):
                print(f"Day {day}: Travel from {city_names[start_val]} to {city_names[end_val]}")
            else:
                print(f"Day {day}: Stay in {city_names[start_val]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()